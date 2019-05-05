use crate::vm::instruction::{Condition, Instruction};
use std::io::{Read, Result as IOResult, Write};

pub mod instruction;

// These should be u16 in sense, but we define as usize for convenience.
pub const KBSR: usize = 0xFE00;
pub const KBDR: usize = 0xFE02;
pub const DSR: usize = 0xFE04;
pub const DDR: usize = 0xFE06;
pub const MCR: usize = 0xFFFE;

const DEFAULT_MEM: [u16; 1 << 16] = {
    let mut mem = [0; 1 << 16];
    mem[DSR] = 0b1000_0000_0000_0000;
    mem[MCR] = 0b1000_0000_0000_0000;
    mem
};

const OPERATING_SYSTEM: &'static [u8] = include_bytes!("../../static/lc3os.obj");

/// A helper struct to handle windows CRLF newline incompatiability
struct CRLFtoLF<T: Read> {
    reader: T,
}

impl<T: Read> Read for CRLFtoLF<T> {
    fn read(&mut self, buf: &mut [u8]) -> IOResult<usize> {
        let size = self.reader.read(buf);
        let newbuf = std::str::from_utf8(buf).unwrap().replace("\x0D", "");
        buf[0..newbuf.len()].copy_from_slice(newbuf.as_bytes());
        size.and(Ok(newbuf.len()))
    }
}

/// A single LC-3 virtual machine.
/// Each machines processes instructions in memory,
/// handling appropriate I/O requests in device registers.
///
/// Note: memory-mapped I/O registers are not implemented as separated fields.
/// The VM will treat device registers as normal words in the mem.
///
/// Note: Currently interrupts are not implemented.
#[derive(Clone)]
pub struct VM {
    /// General purpose registers(R0~R7)
    pub register: [i16; 8],
    /// Program Counter
    pub pc: u16,
    /// Instruction Register
    pub ir: u16,
    /// Supervisor mode
    pub supervisor: bool,
    /// Priority Level(PL0~PL7)
    pub priority: u8,
    /// Condition codes
    pub condition: Condition,
    /// Computer memory
    pub mem: [u16; 1 << 16],
}

impl VM {
    /// Returns a new, initialized LC-3 machine, with default operating system loaded.
    pub fn new() -> VM {
        let mut vm = VM {
            pc: 0x3000,
            ..Default::default()
        };
        vm.load_u8(OPERATING_SYSTEM);
        vm
    }

    /// Loads a program from raw u8 slice(generally, file contents).
    /// # Panics
    /// This function panics if `program` slice's length is not even or less than two(invalid header).
    pub fn load_u8(&mut self, program: &[u8]) {
        let mut chunks = program.chunks(2);
        let header = chunks.next().unwrap();
        let orig = (((header[0] as u16) << 8) + header[1] as u16).into();
        self.load_u16(
            orig,
            chunks
                .map(|x| ((x[0] as u16) << 8) + x[1] as u16)
                .collect::<Vec<_>>()
                .as_ref(),
        );
    }

    /// Loads a program from given path of file.
    /// # Panics
    /// This function panics if file contents' length is not even or less than two(invalid header).
    pub fn load_file(&mut self, path: &std::path::Path) -> std::io::Result<()> {
        let program = std::fs::read(path)?;
        self.load_u8(&program);
        Ok(())
    }

    /// Loads a program from u16 slice from entry point given, and set pc to it.
    /// All other load_* wrappers should convert given input program into u16 slice,
    /// and pass it to this method at the last.
    /// # Panics
    /// This function panics if program size exceeds machine memory range.
    /// (`entry + program.len() >= 65536`)
    pub fn load_u16(&mut self, entry: usize, program: &[u16]) {
        self.mem[entry..(entry + program.len())].copy_from_slice(program);
        self.pc = entry as u16;
    }

    /// Calculates, and returns processor state register(PSR) value.
    pub fn psr(&self) -> u16 {
        ((if self.supervisor { 0 } else { 1 << 15 })
            + ((self.priority as u16 & 0b111) << 8)
            + (if self.condition.n { 1 << 2 } else { 0 })
            + (if self.condition.z { 1 << 1 } else { 0 })
            + (if self.condition.p { 1 } else { 0 })) as u16
    }

    /// Fetches an instruction from `self.mem[self.pc]`, into IR, and increments pc.
    fn fetch(&mut self) {
        self.ir = self.mem[self.pc as usize];
        self.pc += 1;
    }

    /// Updates condition code with given register.
    fn update_condition(&mut self, reg: usize) {
        self.condition.n = self.register[reg] < 0;
        self.condition.z = self.register[reg] == 0;
        self.condition.p = self.register[reg] > 0;
    }

    /// Handles loaded instruction in IR
    fn process_instruction<F, G>(&mut self, mut preld: Option<F>, mut postst: Option<G>)
    where
        F: FnMut(&mut Self, usize) -> (),
        G: FnMut(&mut Self, usize) -> (),
    {
        macro_rules! reg {
            ($num:expr) => {
                self.register[$num as usize]
            };
        }

        macro_rules! zero_if_eq {
            ($addr:expr, $data:expr, $status:expr) => {
                if $addr == $data {
                    self.mem[$status] = 0;
                    /*
                    println!(
                        "{}, {}, {}, 0x{:04X}",
                        stringify!($addr),
                        stringify!($data),
                        stringify!($status),
                        self.mem[$data]
                    );
                    */
                }
            };
        }

        let instruction = Instruction::from_u16(self.ir);

        #[cfg(feature = "instruction-trace")]
        eprintln!("[DEBUG] {:?}", instruction);

        match instruction {
            Instruction::ADD { dst, src1, src2 } => {
                reg!(dst) = reg!(src1).wrapping_add(reg!(src2));
                self.update_condition(dst as usize);
            }
            Instruction::ADDi { dst, src, immd } => {
                reg!(dst) = reg!(src).wrapping_add(immd);
                self.update_condition(dst as usize);
            }
            Instruction::AND { dst, src1, src2 } => {
                reg!(dst) = reg!(src1) & reg!(src2);
                self.update_condition(dst as usize);
            }
            Instruction::ANDi { dst, src, immd } => {
                reg!(dst) = reg!(src) & immd;
                self.update_condition(dst as usize);
            }
            Instruction::BR { cond, offset } => {
                if cond.satisfies(&self.condition) {
                    self.pc = self.pc.wrapping_add(offset as u16);
                }
            }
            Instruction::JMP { base } => {
                self.pc = reg!(base) as u16;
            }
            Instruction::JSR { offset } => {
                reg!(7) = self.pc as i16;
                self.pc = self.pc.wrapping_add(offset as u16);
            }
            Instruction::JSRR { base } => {
                reg!(7) = self.pc as i16;
                self.pc = reg!(base) as u16;
            }
            Instruction::LD { dst, offset } => {
                let addr = (self.pc.wrapping_add(offset as u16)) as usize;

                if let Some(ref mut func) = preld {
                    func(self, addr);
                }

                reg!(dst) = self.mem[addr] as i16;
                self.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LDI { dst, offset } => {
                let addr = self.mem[(self.pc.wrapping_add(offset as u16)) as usize] as usize;

                if let Some(ref mut func) = preld {
                    func(self, addr);
                }

                reg!(dst) = self.mem[addr] as i16;
                self.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LDR { dst, base, offset } => {
                let addr = reg!(base).wrapping_add(offset) as usize;

                if let Some(ref mut func) = preld {
                    func(self, addr);
                }

                reg!(dst) = self.mem[addr] as i16;
                self.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LEA { dst, offset } => {
                reg!(dst) = (self.pc as i16).wrapping_add(offset);
                self.update_condition(dst as usize);
            }
            Instruction::NOT { dst, src } => {
                reg!(dst) = !reg!(src);
                self.update_condition(dst as usize);
            }
            Instruction::RTI => unimplemented!(), // TODO
            Instruction::ST { src, offset } => {
                let addr = (self.pc.wrapping_add(offset as u16)) as usize;
                self.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                if let Some(ref mut func) = postst {
                    func(self, addr);
                }
            }
            Instruction::STI { src, offset } => {
                let addr = self.mem[(self.pc.wrapping_add(offset as u16)) as usize] as usize;
                self.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                if let Some(ref mut func) = postst {
                    func(self, addr);
                }
            }
            Instruction::STR { src, base, offset } => {
                let addr = reg!(base).wrapping_add(offset) as usize;
                self.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                if let Some(ref mut func) = postst {
                    func(self, addr);
                }
            }
            Instruction::RESERVED => unimplemented!(),
            Instruction::TRAP { vect } => {
                reg!(7) = self.pc as i16;
                self.pc = self.mem[(vect as u16) as usize];
            }
        }
    }

    /// Executes next single instruction.
    /// This function does not care about the clock enable bit.
    pub fn step(&mut self) {
        self.fetch();
        self.process_instruction(None::<fn(&mut _, _)>, None::<fn(&mut _, _)>);
    }

    /// Executes next n instructions.
    /// This function does not care about the clock enable bit.
    pub fn step_n(&mut self, n: usize) {
        for _ in 0..n {
            self.step();
        }
    }

    /// Executes next single instruction, with given closures
    /// passed into `process_instruction`.
    /// This function does not care about the clock enable bit.
    pub fn step_with_hook<F, G>(&mut self, pre_load: F, post_store: G)
    where
        F: FnMut(&mut Self, usize),
        G: FnMut(&mut Self, usize),
    {
        self.fetch();
        self.process_instruction(Some(pre_load), Some(post_store));
    }

    /// Executes as much as instructions, while the clock enable bit is set to 1.
    ///
    /// Returns the number of instructions executed.
    ///
    /// Note: This function does not take care of KBSR/DSR, so the VM will run forever
    /// if the program calls I/O subroutines.
    pub fn run(&mut self) -> usize {
        let mut steps = 0;
        while self.mem[MCR] >> 15 > 0 {
            self.step();
            steps += 1;
        }
        steps
    }

    /// Executes next n instructions at maximum, while
    /// the clock enable bit is set to 1.
    ///
    /// Returns the number of instructions executed.
    ///
    /// Note: This function does not take care of KBSR/DSR, so the VM will run forever
    /// if the program calls I/O subroutines.
    pub fn run_n(&mut self, n: usize) -> usize {
        let mut steps = 0;
        while self.mem[MCR] >> 15 > 0 && steps < n {
            self.step();
            steps += 1;
        }
        steps
    }

    /// Executes as much as instructions, while the clock enable bit is set to 1.
    /// Additionally, handles input/output with given streams before each steps.
    ///
    /// Returns the number of instructions executed.
    pub fn run_with_io<'a>(&'a mut self, input: &mut Read, output: &mut Write) -> usize {
        let mut steps = 0;

        #[cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]
        let input = &mut CRLFtoLF { reader: input }; // Wrap input to replace CRLF to LF

        let mut in_stream = input.bytes();

        while self.mem[MCR] >> 15 > 0 {
            if self.mem[DSR] >> 15 == 0 {}

            if self.mem[KBSR] >> 15 == 0 {}

            #[cfg(feature = "register-trace")]
            let pc = self.pc;

            self.step_with_hook(
                |this, addr| {
                    // println!("pre_load 0x{:04X}", addr);
                    if addr == KBSR {
                        if let Some(result) = in_stream.next() {
                            this.mem[KBSR] |= 0b1000_0000_0000_0000;
                            // println!("Got input: 0x{:02X}", result.as_ref().unwrap());
                            this.mem[KBDR] = result.unwrap() as u16;
                        }
                    }
                },
                |this, addr| {
                    // println!("post_store 0x{:04X}", addr);
                    if addr == DDR {
                        // println!("out: 0x{:02X}", this.mem[DDR] as u8);
                        output.write_all(&[this.mem[DDR] as u8]).unwrap();
                        this.mem[DSR] |= 0b1000_0000_0000_0000;
                    }
                },
            );

            #[cfg(feature = "register-trace")]
            eprintln!(
                "[DEBUG] PC=0x{:04X}, IR=0x{:04X}, POST_REG={:04X?}",
                pc, self.ir, self.register
            );
            steps += 1;
        }
        steps
    }

    /// Executes next n instructions as maximum, while the clock enable bit is set to 1.
    /// Additionally, handles input/output with given streams before each steps.
    ///
    /// Returns the number of instructions executed.
    pub fn run_n_with_io<'a>(&mut self, n: usize, input: &mut Read, output: &mut Write) -> usize {
        let mut steps = 0;

        #[cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]
        let input = &mut CRLFtoLF { reader: input }; // Wrap input to replace CRLF to LF

        let mut in_stream = input.bytes();

        while self.mem[MCR] >> 15 > 0 && steps < n {
            if self.mem[DSR] >> 15 == 0 {}

            if self.mem[KBSR] >> 15 == 0 {}

            #[cfg(feature = "register-trace")]
            let pc = self.pc;

            self.step_with_hook(
                |this, addr| {
                    // println!("pre_load 0x{:04X}", addr);
                    if addr == KBSR {
                        if let Some(result) = in_stream.next() {
                            this.mem[KBSR] |= 0b1000_0000_0000_0000;
                            // println!("Got input: 0x{:02X}", result.as_ref().unwrap());
                            this.mem[KBDR] = result.unwrap() as u16;
                        }
                    }
                },
                |this, addr| {
                    // println!("post_store 0x{:04X}", addr);
                    if addr == DDR {
                        // println!("out: 0x{:02X}", this.mem[DDR] as u8);
                        output.write_all(&[this.mem[DDR] as u8]).unwrap();
                        this.mem[DSR] |= 0b1000_0000_0000_0000;
                    }
                },
            );

            #[cfg(feature = "register-trace")]
            eprintln!(
                "[DEBUG] PC=0x{:04X}, IR=0x{:04X}, POST_REG={:04X?}",
                pc, self.ir, self.register
            );
            steps += 1;
        }
        steps
    }
}

impl Default for VM {
    /// Returns empty, zero-filled virtual machine
    fn default() -> VM {
        VM {
            register: [0; 8],
            pc: 0x0000,
            ir: 0x0000,
            supervisor: false,
            priority: 0,
            condition: Default::default(),
            mem: DEFAULT_MEM,
        }
    }
}

#[test]
fn test_update_condition() {
    let mut vm = VM::default();

    vm.register[0] = 0xFF33u16 as i16;
    vm.update_condition(0);
    assert!(vm.condition.n);

    vm.register[2] = 0x0F33i16;
    vm.update_condition(2);
    assert!(vm.condition.p);

    vm.register[1] = 0x0000;
    vm.update_condition(1);
    assert!(vm.condition.z);
}

#[test]
fn test_step() {
    let mut vm = VM::default();
    // ADD R1, R1, #0
    vm.load_u16(0x3000, &[0x1260]);
    vm.step();
    assert!(vm.condition.z);
}

#[test]
fn test_step_n() {
    let mut vm = VM::default();
    // AND R0, R0 #0
    // ADD R0, R0, #14
    vm.load_u16(0x3000, &[0x5020, 0x102E]);
    vm.step_n(2);
    assert_eq!(vm.register[0], 14);
}

#[test]
fn test_run() {
    use std::io::{empty, sink};
    let mut vm = VM::new();
    //      AND R0, R0, #0
    //      AND R1, R1, #0
    //      ADD R0, R0, #3
    // LOOP BRz BYE
    //      ADD R1, R1, #2
    //      ADD R0, R0, #-1
    //      BRnzp   LOOP
    // BYE  STI  R1, SAVE
    //      HALT
    // SAVE .FILL   x3100
    vm.load_u16(
        0x3000,
        &[
            0x5020, 0x5260, 0x1023, 0x0403, 0x1262, 0x103F, 0x0FFC, 0xB201, 0xF025, 0x3100,
        ],
    );
    vm.run_with_io(&mut empty(), &mut sink());
    assert_eq!(vm.mem[0x3100], 6);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load() {
        VM::new();
        VM::default().load_u8(OPERATING_SYSTEM);
        VM::default().load_u8(&[0xFF, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF]);
        VM::default().load_u16(0x3000, &[0, 0, 0, 0]);
    }

    #[test]
    #[should_panic]
    fn test_load_panic() {
        VM::default().load_u8(OPERATING_SYSTEM[1..].as_ref());
        VM::default().load_u8(&[0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF]);
        VM::default().load_u8(&[0xFF, 0xFF, 0xFF, 0xFE, 0xFF]);
        VM::default().load_u16(0xFFFF, &[0, 0, 0, 0]);
    }

}
