use crate::vm::instruction::{Condition, Instruction};
use std::io::{Read, Result as IOResult, Write};

#[cfg(test)]
use std::io::{empty, sink};

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

const OPERATING_SYSTEM: &[u8] = include_bytes!("../../static/lc3os.obj");

/// A helper struct to handle windows CRLF newline incompatiability
struct CRLFtoLF<'a, T> {
    reader: &'a mut T,
}

impl<'a, T> Read for CRLFtoLF<'a, T>
where
    T: Read,
{
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
        let orig = (((u16::from(header[0])) << 8) + u16::from(header[1])).into();
        self.load_u16(
            orig,
            chunks
                .map(|x| ((u16::from(x[0])) << 8) + u16::from(x[1]))
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
            + ((u16::from(self.priority) & 0b111) << 8)
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
    fn process_instruction<'a, R: Read, W: Write>(&mut self, input: &'a mut R, output: &'a mut W) {
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

        let mut in_stream = input.bytes();

        macro_rules! handle_input {
            ($addr:expr) => {
                if $addr == KBSR {
                    if let Some(result) = in_stream.next() {
                        self.mem[KBSR] |= 0b1000_0000_0000_0000;
                        self.mem[KBDR] = u16::from(result.unwrap());
                    }
                }
            };
        }

        macro_rules! handle_output {
            ($addr:expr) => {
                if $addr == DDR {
                    output.write_all(&[self.mem[DDR] as u8]).unwrap();
                    self.mem[DSR] |= 0b1000_0000_0000_0000;
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
                handle_input!(addr);

                reg!(dst) = self.mem[addr] as i16;
                self.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LDI { dst, offset } => {
                let addr = self.mem[(self.pc.wrapping_add(offset as u16)) as usize] as usize;
                handle_input!(addr);

                reg!(dst) = self.mem[addr] as i16;
                self.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LDR { dst, base, offset } => {
                let addr = (reg!(base) as u16).wrapping_add(offset as u16) as usize;
                handle_input!(addr);

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

                handle_output!(addr);
            }
            Instruction::STI { src, offset } => {
                let addr = self.mem[(self.pc.wrapping_add(offset as u16)) as usize] as usize;
                self.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                handle_output!(addr);
            }
            Instruction::STR { src, base, offset } => {
                let addr = (reg!(base) as u16).wrapping_add(offset as u16) as usize;
                self.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                handle_output!(addr);
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
    pub fn step<'a, R: Read, W: Write>(&mut self, input: &'a mut R, output: &'a mut W) {
        self.fetch();
        self.process_instruction(input, output);
    }

    /// Executes next n instructions.
    /// This function does not care about the clock enable bit.
    pub fn step_n<'a, R: Read, W: Write>(&mut self, input: &'a mut R, output: &'a mut W, n: usize) {
        for _ in 0..n {
            self.step(input, output);
        }
    }

    /// Executes as much as instructions, while the clock enable bit is set to 1.
    ///
    /// Returns number of instructions executed.
    pub fn run<'a, R: Read, W: Write>(&mut self, input: &'a mut R, output: &'a mut W) -> usize {
        let mut steps = 0;
        while self.mem[MCR] >> 15 > 0 {
            self.step(input, output);
            steps += 1;
        }
        steps
    }

    /// Executes next n instructions at maximum, while
    /// the clock enable bit is set to 1.
    ///
    /// Returns the number of instructions executed.
    pub fn run_n<'a, R: Read, W: Write>(
        &mut self,
        input: &'a mut R,
        output: &'a mut W,
        n: usize,
    ) -> usize {
        #[cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]
        let input = &mut CRLFtoLF { reader: input }; // Wrap input to replace CRLF to LF

        let mut steps = 0;
        while self.mem[MCR] >> 15 > 0 && steps < n {
            #[cfg(feature = "register-trace")]
            let pc = self.pc;

            self.step(input, output);

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
    vm.step(&mut empty(), &mut sink());
    assert!(vm.condition.z);
}

#[test]
fn test_step_n() {
    let mut vm = VM::default();
    // AND R0, R0 #0
    // ADD R0, R0, #14
    vm.load_u16(0x3000, &[0x5020, 0x102E]);
    vm.step_n(&mut empty(), &mut sink(), 2);
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
    vm.run(&mut empty(), &mut sink());
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
