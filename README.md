# RUSTCHECK: Safety Enhancement of the Unsafe Rust
RUSTCHEKCK enhances the safety of unsafe Rust, and helps Rust developers effectively diagnose the root causes of
memory-related bugs.


## Install
Currently supports rustc version: rustc 1.57.0-nightly (dfc5add91 2021-10-13)
```
$ git clone https://github.com/RUSTCHECK/rustcheck.git
$ cd rustcheck
$ rustup component add rust-src
$ rustup component add rustc-dev
$ rustup component add llvm-tools-preview
```

## Example
Test examples
```
$ ./run.sh examples/table
$ ./example/table/target/debug/table
```

Rust provides the unsafe feature to allow Rust developers to write insecure code. It may lead to memory safety vulnerabilities, Even worse, once a Rust program crashes, it is difficult to diagnose the root causes.
RUSTCHECK takes the following key steps to diagnose bugs:

	1) it performs static program analysis to identify possible insecure patterns;
 	2) it inserts necessary runtime checks against the identified insecure patterns;
	3) it re-executes the instrumented Rust programs to identify the root causes of the bugs or crashes.

## Acknowledgement
We learned a lot from the following projects when building prototype system.
- [rust-lock-bug-detector](https://github.com/BurtonQin/rust-lock-bug-detector): the code frame.

