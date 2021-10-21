#![allow(warnings, unused, dead_code)]
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::sync::Mutex;
use std::ptr;
// the embedded code 
// ============================================================
lazy_static! {
    static ref TABLE: Mutex<HashMap<usize, usize>> = Mutex::new(HashMap::new());
}

pub fn unsafe_fn() {
    let mut item = 123;
    unsafe{
        std::ptr::drop_in_place(&mut item);
    }
}

pub fn table_insert(ptr: *const u8) {
    println!("try to insert 0x{:x}...", ptr as usize);
    let len = 1;
    TABLE.lock().unwrap().insert(ptr as usize, len);
    println!("inserted...");
}

pub fn table_delete(ptr: *const u8) {
    println!("try to delete 0x{:x}...", ptr as usize);
    let uptr = ptr as usize;
    let len = table_query(ptr);
    if !(len > 0) {
        println!("***do not double free 0x{:x}...***", ptr as usize);
        std::process::exit(0x0100)
    }
    // assert!(len > 0, "***double free***");
    TABLE.lock().unwrap().remove(&uptr);
    println!("deleted...");
}

pub fn table_query(ptr: *const u8) -> usize {  
    println!("try to query 0x{:x}...", ptr as usize);
    let uptr = ptr as usize;
    let len = match TABLE.lock().unwrap().get(&uptr) {
        Some(v) => *v,
        None => 0,
    };
    if len == 0 {
       println!("query failed...");
    } else {
       println!("got it...");
    }
    len
}

// pub fn table_lookup(ptr: *const u8, var: String, position: String) {
pub fn table_lookup(ptr: *const u8) {
    unsafe{
    println!("try to lookup 0x{:x}...", ptr as usize);
    }
    let result = table_query(ptr);
    // assert!(result != 0, "***use after free***");
    // assert!(result < len, "***out-of-bound access***");
    if result == 0 {
        println!("do not use 0x{:x} after free...", ptr as usize);
        std::process::exit(0x0100);
    }
    println!("lookup done...");
}

pub fn print_table() {
    println!("try to print table");
    let hash = TABLE.lock().unwrap();
    for (key, value) in hash.iter() {
        println!("key:{:?} value :{:?}", key, value);
    }
    println!("printed...");
}

// ============================================================

// test cases.
// ============================================================

// fn test_bound_check() {
//     let array = [1, 2, 3, 4];
//     // array[4];
//     unsafe {
//         let ptr = array.as_ptr().offset(4);
//         println!("{}", *ptr);
//     }
// }


fn string_test_use_after_free() -> String {
    let mut s = String::from("use_after_free");
    let ptr = s.as_mut_ptr();
    let mut s1;
    unsafe {
        s1 = String::from_raw_parts(ptr, s.len(), s.len());
    }
    return s1;
}

// double free
fn string_test_double_free() {
    let mut s = String::from("double_free");
    let ptr = s.as_mut_ptr();
    let s1;
    unsafe {
        s1 = String::from_raw_parts(ptr, s.len(), s.len());
    }

}

pub struct PanicsOnDrop (u32, bool);

pub fn new_PanicsOnDrop() -> PanicsOnDrop {
    return PanicsOnDrop(123, true);
}

impl Drop for PanicsOnDrop {
    fn drop(&mut self) {
        println!("Dropping {}", self.0);
        if self.1 {
            self.1 = false;
            panic!("Panicking on drop");
        }
    }
}

fn test_df_PanicsOnDrop() {
    let mut item = new_PanicsOnDrop();

    unsafe{
        std::ptr::drop_in_place(&mut item);
    }
}


// ============================================================

fn main() {
    // string_test_double_free();
    // string_test_use_after_free();
    test_df_PanicsOnDrop();
}
