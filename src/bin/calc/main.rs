use lc3::vm::VM;
use std::io;

fn main() {
    let mut vm = VM::new();
    vm.load_u8(include_bytes!("static/calc.obj"));
    vm.run_with_io(&mut io::stdin().lock(), &mut io::stdout().lock());
}
