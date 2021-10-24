#![feature(rustc_private)]
#![feature(box_patterns)]
#![allow(warnings, unused, dead_code)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
use std::convert::TryInto;
use rustc_driver::Compilation;
use rustc_hir as hir;
use rustc_hir::def_id;
use rustc_hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use rustc_hir::hir_id::HirId;
use rustc_index::vec::Idx;
use rustc_index::vec::IndexVec;
use rustc_middle::mir;
use rustc_middle::{
    mir::{
        interpret::ConstValue,
        interpret::{LitToConstInput, Scalar},
        visit::Visitor,
        BasicBlock, BasicBlockData, Body, Constant, HasLocalDecls, Local, LocalDecl, Location,
        Mutability, Operand, Place, Rvalue, SourceInfo, SourceScope, Statement, StatementKind,
        Terminator, TerminatorKind,
    },
    ty::{subst::GenericArg, Const, ConstKind, List, TyCtxt, TyKind, UserTypeAnnotationIndex},
};
use rustc_session::config::ErrorOutputType;
use rustc_session::early_error;
use rustc_span::{hygiene::SyntaxContext, BytePos, Span};

struct RustCheckCallbacks;

impl rustc_driver::Callbacks for RustCheckCallbacks {
    /// All the work we do happens after analysis, so that we can make assumptions about the validity of the MIR.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        enter_with_fn(queries, mir_analysis);
        compiler.session().abort_if_errors();
        Compilation::Continue
    }
}

/// Call a function which takes the `TyCtxt`.
fn enter_with_fn<'tcx, TyCtxtFn>(queries: &'tcx rustc_interface::Queries<'tcx>, enter_fn: TyCtxtFn)
where
    TyCtxtFn: Fn(TyCtxt),
{
    queries.global_ctxt().unwrap().peek_mut().enter(enter_fn);
}

/// Perform the RustCheck
fn mir_analysis(tcx: TyCtxt) {
    let ids = tcx.mir_keys(());
    // the prototype processes the crate named "table".
    let crate_name = tcx.crate_name(rustc_span::def_id::CrateNum::from_usize(0)).to_ident_string();
    if crate_name != String::from("table") {
        return ;
    }
    let fn_ids: Vec<LocalDefId> = ids
        .clone()
        .into_iter()
        .filter(|id| {
            let hir = tcx.hir();
            hir.body_owner_kind(hir.local_def_id_to_hir_id(*id))
                .is_fn_or_closure()
        })
        .collect();
        
    // des_ids [insert, delete, lookup, query]
    let mut des_ids: [LocalDefId; 4] = [LocalDefId::new(0); 4];

    // Collect the table-operartion function and unsafe function. 
    // ============================================================
    for fn_id in &fn_ids {
        let name;
        let hir_id = tcx.hir().local_def_id_to_hir_id(*fn_id);
        if let Some(fname) = tcx.hir().opt_name(hir_id) {
            name = fname.to_ident_string()
        } else {
            name = String::from("");
        }
        match &name[..] {
            "table_insert" => {
                dbg!(String::from("we found table_insert !"));
                des_ids[0] = *fn_id;
            }
            "table_delete" => {
                dbg!(&String::from("we found table_delete !"));
                des_ids[1] = *fn_id;
            }
            "table_lookup" => {
                dbg!(&String::from("we found table_lookup !"));
                des_ids[2] = *fn_id;
            }
            "table_query" => {
                dbg!(&String::from("we found table_query !"));
                des_ids[3] = *fn_id;
            }
            _ => {}
        }
    }
    // ============================================================

    for fn_id in &fn_ids {
        let name;
        let hir_id = tcx.hir().local_def_id_to_hir_id(*fn_id);
        if let Some(fname) = tcx.hir().opt_name(hir_id) {
            name = fname.to_ident_string()
        } else {
            name = String::from("");
        }
        // skip the table operation function
        if (name == String::from("table_insert") 
            || name == String::from("table_delete")
            || name == String::from("table_lookup")
            || name == String::from("table_query"))  {
            continue;
        }
        
        if name.starts_with("string_test") {
            let body = tcx.optimized_mir(*fn_id);
            let basic_blocks = body.basic_blocks();
            let local_decls = &body.local_decls;
            let var_debug_info = &body.var_debug_info;
            for (id, block_data) in basic_blocks.iter_enumerated() {
                let terminator = block_data.terminator();
                // the index of basic blocks
                let index = id.index();

                match &terminator.kind {

                    // add table_lookup call.
                    TerminatorKind::Return => {
                        if return_empty(body.return_ty(), &tcx) {
                            continue;
                        }
                        
                        let mut args: Vec<Operand> = Vec::new();
                        args.push(Operand::Copy(Place::from(Local::from_usize(0))));
                        let line = get_line(&tcx, &var_debug_info, 0);
                        args.push(gen_u32_args(&tcx, line));
                        // get table table_lookup.
                        let func = new_fn_call(2, &tcx, &des_ids);

                        // declare a new var, which holds function return.
                        let mlocal = new_unit(&local_decls, &tcx);
                        change_block(&block_data, basic_blocks, &func, index, mlocal, args);
                    }

                    // add table_insert call.
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        cleanup,
                        from_hir_call,
                        fn_span,
                    } => {

                        let (place, bb) = destination.unwrap();
                        // if function return a struct, we insert its address to the table.
                        if let rustc_middle::ty::TyKind::Adt(adt_def, adt_ref) = local_decls[place.local].ty.kind() {
                            if adt_def.is_struct() {

                                // make table function's args
                                let mut args: Vec<Operand> = Vec::new();
                                args.push(Operand::Copy(place));

                                // prepare for the table_insert call
                                let func = new_fn_call(0, &tcx, &des_ids);
                                let mlocal = new_unit(&local_decls, &tcx);
                                let block_data = &basic_blocks[bb];
                                change_block(&block_data, basic_blocks, &func, bb.index(), mlocal, args);
                            }
                        }
                    }

                    _ => {}
                }
            }
            
            for (id, block_data) in basic_blocks.iter_enumerated() {
                let terminator = block_data.terminator();
                // the index of basic blocks
                let index = id.index();
                // add table_delete call
                match &terminator.kind {
                    TerminatorKind::Drop {
                        place,
                        target,
                        unwind,
                    } => {
                        let mut args: Vec<Operand> = Vec::new();
                        args.push(Operand::Copy(*place));
                        // dbg!(place.local.as_usize());
                        let line = get_line(&tcx, &var_debug_info, place.local.as_u32());
                        args.push(gen_u32_args(&tcx, line));
                        // prepare for the table_delete call
                        let func = new_fn_call(1, &tcx, &des_ids);
                        let mlocal = new_unit(&local_decls, &tcx);
                        change_block(&block_data, basic_blocks, &func, index, mlocal, args);
                    }

                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        cleanup,
                        from_hir_call,
                        fn_span,
                    } => {
                        // we skip it when Call is not drop_in_place.
                        if match_fn_def(func, 2, 2505) == false {
                            continue;
                        }
                        // prepare for the table_delete call
                        let mut args = args.to_vec();
                        if let rustc_middle::mir::Operand::Move(place) = &args[0] {
                            let line = get_line(&tcx, &var_debug_info, place.local.as_u32());
                            args.push(gen_u32_args(&tcx, line));
                        }
                        let func = new_fn_call(1, &tcx, &des_ids);
                        let mlocal = new_unit(&local_decls, &tcx);
                        change_block(&block_data, basic_blocks, &func, index, mlocal, args);
                    }

                    _ => {}
                }
            }
        }
        if name.starts_with("test") {
            let body = tcx.optimized_mir(*fn_id);
            let basic_blocks = body.basic_blocks();
            let local_decls = &body.local_decls;
            let var_debug_info = &body.var_debug_info;
            for (id, block_data) in basic_blocks.iter_enumerated() {
                let terminator = block_data.terminator();
                // the index of basic blocks
                let index = id.index();

                
                match &terminator.kind {

                    // add table_lookup call.
                    TerminatorKind::Return => {
                        if return_empty(body.return_ty(), &tcx) {
                            continue;
                        }
                        
                        // declare a new variable.
                        let mlocal = new_const_u8_decl(&local_decls, &tcx);

                        // add assign statements to basicblocks[indedx].statements.
                        add_new_assign_stmt(mlocal, 0, index, &basic_blocks);

                        // make table function's args
                        let mut args: Vec<Operand> = Vec::new();
                        args.push(Operand::Copy(Place::from(Local::from_usize(mlocal))));
                        let line = get_line(&tcx, &var_debug_info, mlocal as u32);
                        args.push(gen_u32_args(&tcx, line));

                        // get table table_lookup.
                        let func = new_fn_call(2, &tcx, &des_ids);

                        // declare a new var, which holds function return.
                        let mlocal = new_unit(&local_decls, &tcx);
                        change_block(&block_data, basic_blocks, &func, index, mlocal, args);
                    }

                    // add table_insert call.
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        cleanup,
                        from_hir_call,
                        fn_span,
                    } => {

                        let (place, bb) = destination.unwrap();
                        // if function return a struct, we insert its address to the table.
                        if let rustc_middle::ty::TyKind::Adt(adt_def, adt_ref) = local_decls[place.local].ty.kind() {
                            if adt_def.is_struct() {

                                // declare a new variable.
                                let mlocal = new_const_u8_decl(&local_decls, &tcx);
                                
                                // make table function's args
                                let mut args: Vec<Operand> = Vec::new();
                                args.push(Operand::Copy(Place::from(Local::from_usize(mlocal))));
                                
                                // add assign statements to basicblocks[indedx].statements.
                                add_new_assign_stmt(mlocal, place.local.as_usize(), index, &basic_blocks);

                                // prepare for the table_insert call
                                let func = new_fn_call(0, &tcx, &des_ids);
                                let mlocal = new_unit(&local_decls, &tcx);
                                let block_data = &basic_blocks[bb];

                                change_block(&block_data, basic_blocks, &func, bb.index(), mlocal, args);
                            }
                        }
                    }

                    _ => {}
                }
            }

            for (id, block_data) in basic_blocks.iter_enumerated() {
                let terminator = block_data.terminator();
                // the index of basic blocks
                let index = id.index();

                // add table_delete call
                match &terminator.kind {
                    TerminatorKind::Return => {}

                    TerminatorKind::Drop {
                        place,
                        target,
                        unwind,
                    } => { 
                        
                        // declare a new variable holding the address of the object to be dropped.
                        let mlocal = new_const_u8_decl(&local_decls, &tcx);
                        
                        let mut args: Vec<Operand> = Vec::new();
                        args.push(Operand::Copy(Place::from(Local::from_usize(mlocal))));
                        let line = get_line(&tcx, &var_debug_info, place.local.as_u32());
                        args.push(gen_u32_args(&tcx, line));

                        // add assign statements to basicblocks[indedx].statements.
                        add_new_assign_stmt(mlocal, place.local.as_usize(), index, &basic_blocks);


                        // prepare for the table_delete call
                        let func = new_fn_call(1, &tcx, &des_ids);
                        let mlocal = new_unit(&local_decls, &tcx);
                        change_block(&block_data, basic_blocks, &func, index, mlocal, args);
                    }

                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        cleanup,
                        from_hir_call,
                        fn_span,
                    } => {
                        // we skip it when Call is not drop_in_place.
                        if match_fn_def(func, 2, 2505) == false {
                            continue;
                        }

                        // prepare for the table_delete call
                        let mut args = args.to_vec();
                        if let rustc_middle::mir::Operand::Move(place) = &args[0] {
                            let line = get_line(&tcx, &var_debug_info, place.local.as_u32());
                            args.push(gen_u32_args(&tcx, line));
                        }
                        
                        let func = new_fn_call(1, &tcx, &des_ids);
                        let mlocal = new_unit(&local_decls, &tcx);
                        change_block(&block_data, basic_blocks, &func, index, mlocal, args);
                    }

                    _ => {}
                }
            }
        }
    }
}

fn main() {
    rustc_driver::init_rustc_env_logger();
    let args = std::env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                early_error(
                    ErrorOutputType::default(),
                    &format!("argument {} is not valid Unicode: {:?}", i, arg),
                )
            })
        })
        .collect::<Vec<_>>();
    run_compiler(args, &mut RustCheckCallbacks)
}

fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        None
    } else {
        let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
        let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
        Some(match (home, toolchain) {
            (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
            _ => option_env!("RUST_SYSROOT")
                .expect("To build this without rustup, set the RUST_SYSROOT env var at build time")
                .to_owned(),
        })
    }
}

fn run_compiler(mut args: Vec<String>, callbacks: &mut (dyn rustc_driver::Callbacks + Send)) -> ! {
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }
    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks).run()
    });
    std::process::exit(exit_code)
}

pub fn change_block<'tcx>(
    block_data: &'tcx BasicBlockData,
    basic_blocks: &'tcx IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    func: &Operand,
    index: usize,
    mlocal: usize,
    args: Vec<Operand>, 
) {
    let terminator = block_data.terminator();
    let new_terminator: Terminator = terminator.clone();
    let mbasic_blocks = unsafe {
        &mut *(basic_blocks as *const IndexVec<BasicBlock, BasicBlockData>
            as *mut IndexVec<BasicBlock, BasicBlockData>)
    };
    let new_block_data = BasicBlockData::new(Some(new_terminator));
    let i = mbasic_blocks.push(new_block_data);
    let new_index = i.index() as u32;
    let mblockdata = mbasic_blocks.get_mut(BasicBlock::from_usize(index));
    let fun = Operand::to_copy(func);
    let local = Local::from_usize(mlocal);
    let destination = Some((Place::from(local), BasicBlock::from_u32(new_index)));
    let cleanup: Option<BasicBlock> = None;
    let from_hir_call = true;
    let fn_span = Span::default();
    let kind = TerminatorKind::Call {
        func: fun,
        args,
        destination,
        cleanup,
        from_hir_call,
        fn_span,
    };
    let source_info = SourceInfo {
        span: Span::default(),
        scope: SourceScope::from_u32(0),
    };
    let t = Terminator { source_info, kind };
    
    if let Some(blockdata) = mblockdata {
        blockdata.terminator = Some(t);
    };
}

pub fn new_const_u8_decl<'tcx>(
    local_decls: &'tcx rustc_middle::mir::LocalDecls,
    tcx: &'tcx rustc_middle::ty::TyCtxt
) -> usize {
    let ty_u8_ptr = tcx.mk_ty(TyKind::RawPtr(rustc_middle::ty::TypeAndMut{
        ty: tcx.mk_ty(TyKind::Uint(rustc_middle::ty::UintTy::U8)),
        mutbl: rustc_middle::mir::Mutability::Not,
    }));
    let local_decl = LocalDecl {
        mutability: rustc_middle::mir::Mutability::Not,
        local_info: None,
        internal: true,
        is_block_tail: None,
        ty: ty_u8_ptr,
        user_ty: None,
        source_info: SourceInfo {
            span: Span::default(),
            scope: SourceScope::from_u32(0),
        },
    };
    let mlocal_decls = unsafe {
        &mut *(local_decls as *const IndexVec<Local, LocalDecl>
            as *mut IndexVec<Local, LocalDecl>)
    };
    let ml = mlocal_decls.push(local_decl);
    let mlocal = ml.index();
    return mlocal;
}

pub fn new_unit<'tcx>(
    local_decls: &'tcx rustc_middle::mir::LocalDecls,
    tcx: &'tcx rustc_middle::ty::TyCtxt
) -> usize {
    let substs_ref: &List<GenericArg> = List::empty();
    let unit = tcx.mk_ty(TyKind::Tuple(substs_ref));
    let local_decl = LocalDecl {
        mutability: Mutability::Mut,
        local_info: None,
        internal: true,
        is_block_tail: None,
        ty: unit,
        user_ty: None,
        source_info: SourceInfo {
            span: Span::default(),
            scope: SourceScope::from_u32(1),
        },
    };
    let mlocal_decls = unsafe {
        &mut *(local_decls as *const IndexVec<Local, LocalDecl>
            as *mut IndexVec<Local, LocalDecl>)
    };
    let ml = mlocal_decls.push(local_decl);
    let mlocal = ml.index();
    return mlocal;
}

pub fn new_fn_call<'tcx>(
    n: usize,
    tcx: &'tcx rustc_middle::ty::TyCtxt,
    des_ids: &'tcx [LocalDefId; 4]
) -> Operand<'tcx> {
    let mconst = tcx.mk_const(Const {
        val: ConstKind::Value(ConstValue::Scalar(Scalar::ZST)),
        ty: tcx.type_of(des_ids[n]),
    });

    let literal = mir::ConstantKind::Ty(mconst);
    let span = Span::default();
    let user_ty: Option<UserTypeAnnotationIndex> = None;
    let func = Operand::Constant(Box::new(Constant {
        span,
        user_ty,
        literal,
    }));
    return func;
}

pub fn add_new_assign_stmt<'tcx>(
    lhs: usize,
    rhs: usize,
    bb_index: usize,
    basic_blocks: &'tcx IndexVec<BasicBlock, BasicBlockData<'tcx>>
) {
    let rvalue = rustc_middle::mir::Rvalue::AddressOf(rustc_middle::mir::Mutability::Not, Place::from(Local::from_usize(rhs)));
    let assign = rustc_middle::mir::StatementKind::Assign(Box::new((Place::from(Local::from_usize(lhs)), rvalue)));
    let stmt = rustc_middle::mir::Statement {
        source_info: SourceInfo {
            span: Span::default(),
            scope: SourceScope::from_u32(1),
        },
        kind: assign,
    };
    let mbasic_blocks = unsafe {
        &mut *(basic_blocks as *const IndexVec<BasicBlock, BasicBlockData>
            as *mut IndexVec<BasicBlock, BasicBlockData>)
    };
    mbasic_blocks[rustc_middle::mir::BasicBlock::from_usize(bb_index)].statements.push(stmt);
}

// get true if the function return type is tuple([]).
pub fn return_empty(return_ty: rustc_middle::ty::Ty, tcx: &rustc_middle::ty::TyCtxt) -> bool {
    let substs_ref: &List<GenericArg> = List::empty();
    let unit = tcx.mk_ty(TyKind::Tuple(substs_ref));
    return return_ty == unit;
}

// func              (krate, index)
// offset              (2, 2377)
// drop_in_place       (2, 2505)
pub fn match_fn_def(func: &rustc_middle::mir::Operand, crate_index: usize, index_index: usize) -> bool {
    if let rustc_middle::mir::Operand::Constant(box(cons)) = func {
        if let rustc_middle::mir::ConstantKind::Ty(fcons) = &cons.literal {
            let fty = &fcons.ty;
            if let rustc_middle::ty::TyKind::FnDef(did, _) = &fty.kind() {
                if did.krate.index() == crate_index && did.index.index() == index_index {
                    return true;
                }
            }
        }
    }
    return false;
}

pub fn get_line(tcx: &TyCtxt, var_debug_info: &Vec<rustc_middle::mir::VarDebugInfo>, var: u32) -> u32 {
    for item in var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &item.value {
            if place.local.as_u32() == var {
                // dbg!(&item.source_info.span.lo());
                let bp = item.source_info.span.lo().clone();
                let sess = &tcx.sess;
                let sm = sess.source_map();
                // dbg!(sm.lookup_line(bp));
                if let Ok(sfal) = sm.lookup_line(bp) {
                    return sfal.line as u32;
                }
            }
        }
    }
    return 0;
}

pub fn gen_u32_args<'a>(tcx: &'a TyCtxt, value: u32) -> Operand<'a> {
    let mconst = tcx.mk_const(Const {
        val: ConstKind::Value(ConstValue::Scalar(Scalar::from_u32(value))),
        ty: tcx.mk_ty(TyKind::Uint(rustc_middle::ty::UintTy::U32)),
    });  
    let literal = mir::ConstantKind::Ty(mconst);
    let span = Span::default();
    let user_ty: Option<UserTypeAnnotationIndex> = None;
    let const_val = Operand::Constant(Box::new(Constant {
        span,
        user_ty,
        literal,
    }));
    return const_val;
}