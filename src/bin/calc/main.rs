#[macro_use]
extern crate rust_embed;

use lc3::vm::VM;
use std::io;

#[derive(RustEmbed)]
#[folder = "src/bin/calc/static/"]
struct Asset;

fn main() {
    let mut vm = VM::new();
    vm.load_u8(Asset::get("calc.obj").unwrap().as_ref());
    vm.run_with_io(&mut io::stdin().lock(), &mut io::stdout().lock());
}
