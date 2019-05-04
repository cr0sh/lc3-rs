# lc3-rs
```
Efficient LC-3 simulator for any platforms, written in pure Rust.
Copyright (C) 2019 Nam Jeonghyun. (ska827@snu.ac.kr)
```

## Usage

Currently there is no useful frontends (e.g. benchmarkers, debuggers) is implemented. You can run simple LC-3 calculator which implements [this specification](http://archi.snu.ac.kr/courses/under/19_spring_computer_concept/slides/proj1.pdf) with `cargo run --bin calc`.

## Using as a library

You can `use lc3::vm` to get your code to handle LC-3 instructions. Please refer to docs.

There are two useful optional features for debugging, `register-trace` and `instruction-trace`.

If `register-trace` feature is enabled, `pc`, `ir`, `register` will be printed into stderr after each steps are executed. Note that `pc` will represent an _actual_ location of the instruction executed(PC is automatically incremented after fetching instructions, therefore `self.pc-1`), but `register` values will be printed _after_ the instruction is executed.

If `instruction-trace` feature is enabled, contents of `ir` will be printed into stderr as a parsed `Instruction` enum _before_ the instruction is executed.

Additionally, on Windows, CRLF line endings will be automatically converted into LF. If you prefer not to do this, enable `disable-crlf-compat-windows` feature when building.

## License

[GPLv2](http://github.com/cr0sh/lc3-rs/blob/master/LICENSE), also refer to [a copyright notice for embedded lc3os.obj](http://github.com/cr0sh/lc3-rs/blob/master/COPYRIGHT).