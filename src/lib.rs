use std::io::{empty, sink, Empty, Error as IOError, Sink};
use std::path::Path;

pub mod instruction;
pub mod iostream_handler;

#[cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]
pub(crate) mod crlf_helper;

pub use instruction::*;
pub use iostream_handler::IOStreamHandler;
use std::fmt::Debug;

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

/*
const OS_LOADED_MEM: [u16; 1 << 16] = {
    // TODO
    let mut mem = [0; 1 << 16];
    mem[DSR] = 0b1000_0000_0000_0000;
    mem[MCR] = 0b1000_0000_0000_0000;
    mem
};
*/

const OPERATING_SYSTEM: &[u8] = include_bytes!("../static/lc3os.obj");

/// An instruction handler interface.
pub trait InstructionHandler
where
    Self: Sized,
{
    /// Handler context.
    type Context;
    /// Err return type after processing instructions.
    /// TODO: Convert `Err` into `std::ops::Try` once it is stabilized
    type Err;

    fn create_vm(initial_context: Self::Context) -> VM<Self>;

    fn process_instruction(
        vm_state: &mut VMState,
        context: &mut Self::Context,
        instruction: Instruction,
    ) -> Result<(), Self::Err>;
}

/// Trivial InstructionHandler implementation, without I/O support
pub struct TrivialHandler;

impl InstructionHandler for TrivialHandler {
    type Context = (Empty, Sink);
    type Err = IOError;

    fn create_vm(_: Self::Context) -> VM<Self> {
        let mut vm = VM {
            state: VMState::default(),
            context: (empty(), sink()),
        };
        vm.load_u8(OPERATING_SYSTEM);
        vm
    }

    fn process_instruction(
        vm_state: &mut VMState,
        context: &mut Self::Context,
        instruction: Instruction,
    ) -> Result<(), Self::Err> {
        IOStreamHandler::process_instruction(vm_state, context, instruction)
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
pub struct VM<H=TrivialHandler>
where
    H: InstructionHandler,
{
    pub state: VMState,
    /// Instruction handler context
    pub context: H::Context,
}

impl<H> VM<H>
where
    H: InstructionHandler,
    H::Err: Debug,
{
    /// Returns a new, initialized LC-3 machine, with default operating system loaded.
    pub fn new(initial_context: H::Context) -> VM<H> {
        H::create_vm(initial_context)
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
    pub fn load_file<P: AsRef<Path>>(&mut self, path: P) -> std::io::Result<()> {
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
        self.state.mem[entry..(entry + program.len())].copy_from_slice(program);
        self.state.pc = entry as u16;
    }

    /// Executes next single instruction.
    /// This function does not care about the clock enable bit.
    pub fn step(&mut self) -> Result<(), H::Err> {
        self.state.fetch();
        let instruction = Instruction::from_u16(self.state.ir);
        H::process_instruction(&mut self.state, &mut self.context, instruction)
    }

    /// Executes next n instructions.
    /// This function does not care about the clock enable bit.
    pub fn step_n(&mut self, n: usize) -> Result<(), H::Err> {
        for _ in 0..n {
            self.step()?;
        }
        Ok(())
    }

    /// Executes as much as instructions, while the clock enable bit is set to 1.
    ///
    /// Returns number of instructions executed if vm was executed without errors until termination,
    /// or returns error immediately when error has occurred.
    pub fn run(&mut self) -> Result<usize, H::Err> {
        let mut steps = 0;
        while self.state.mem[MCR] >> 15 > 0 {
            self.step()?;
            steps += 1;
        }
        Ok(steps)
    }

    /// Executes next n instructions at maximum, while
    /// the clock enable bit is set to 1.
    ///
    /// Returns number of instructions executed if vm was executed without errors until termination,
    /// or returns error immediately when error has occurred.
    pub fn run_n(&mut self, n: usize) -> Result<usize, H::Err> {
        let mut steps = 0;
        while self.state.mem[MCR] >> 15 > 0 && steps < n {
            #[cfg(feature = "register-trace")]
            let pc = self.pc;

            self.step()?;

            #[cfg(feature = "register-trace")]
            eprintln!(
                "[DEBUG] PC=0x{:04X}, IR=0x{:04X}, POST_REG={:04X?}",
                pc, self.state.ir, self.state.register
            );

            steps += 1;
        }
        Ok(steps)
    }
}

impl Default for VM<TrivialHandler> {
    fn default() -> Self {
        Self {
            state: Default::default(),
            context: (empty(), sink()),
        }
    }
}

/// A VM state.
#[derive(Clone)]
pub struct VMState {
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

impl VMState {
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
    /// Note that each instruction handler should call this explicitly if needed.
    fn update_condition(&mut self, reg: usize) {
        self.condition.n = self.register[reg] < 0;
        self.condition.z = self.register[reg] == 0;
        self.condition.p = self.register[reg] > 0;
    }
}

impl Default for VMState {
    /// Returns empty, zero-filled virtual machine status with default memory filled.
    fn default() -> Self {
        VMState {
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

    vm.state.register[0] = 0xFF33u16 as i16;
    vm.state.update_condition(0);
    assert!(vm.state.condition.n);

    vm.state.register[2] = 0x0F33i16;
    vm.state.update_condition(2);
    assert!(vm.state.condition.p);

    vm.state.register[1] = 0x0000;
    vm.state.update_condition(1);
    assert!(vm.state.condition.z);
}

#[test]
fn test_step() {
    let mut vm = VM::default();
    // ADD R1, R1, #0
    vm.load_u16(0x3000, &[0x1260]);
    vm.step().unwrap();
    assert!(vm.state.condition.z);
}

#[test]
fn test_step_n() {
    let mut vm = VM::default();
    // AND R0, R0 #0
    // ADD R0, R0, #14
    vm.load_u16(0x3000, &[0x5020, 0x102E]);
    vm.step_n(2).unwrap();
    assert_eq!(vm.state.register[0], 14);
}

#[test]
fn test_run() {
    let mut vm = VM::default();
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
    vm.run().unwrap();
    assert_eq!(vm.state.mem[0x3100], 6);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load() {
        VM::default();
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
