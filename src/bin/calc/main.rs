use lc3::{IOStreamHandler, VM};
use std::io;

fn main() {
    let mut vm = VM::<IOStreamHandler<_, _>>::new((io::stdin(), io::stdout()));
    vm.load_u8(include_bytes!("static/calc.obj"));
    vm.run().unwrap();
}
