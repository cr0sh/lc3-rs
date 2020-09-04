use crate::{Instruction, InstructionHandler, VMState, DDR, DSR, KBDR, KBSR, OPERATING_SYSTEM, VM};
use std::io::{Error as IOError, Read, Result as IOResult, Write};
use std::marker::PhantomData;

#[cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]
use crate::crlf_helper::CRLFtoLF;

/// A standard instruction handler with Read/Write streams for input/output.
pub struct IOStreamHandler<R: Read, W: Write> {
    phantom_r: PhantomData<R>,
    phantom_w: PhantomData<W>,
}

impl<R: Read, W: Write> InstructionHandler for IOStreamHandler<R, W> {
    type Context = (R, W);
    type Err = IOError;

    fn create_vm(initial_context: Self::Context) -> VM<Self> {
        let mut vm = VM {
            state: Default::default(),
            context: initial_context,
        };
        vm.load_u8(OPERATING_SYSTEM);
        vm
    }

    fn process_instruction(
        vm_state: &mut VMState,
        context: &mut Self::Context,
        instruction: Instruction,
    ) -> IOResult<()> {
        macro_rules! reg {
            ($num:expr) => {
                vm_state.register[$num as usize]
            };
        }

        macro_rules! zero_if_eq {
            ($addr:expr, $data:expr, $state:expr) => {
                if $addr == $data {
                    vm_state.mem[$state] = 0;
                    /*
                    println!(
                        "{}, {}, {}, 0x{:04X}",
                        stringify!($addr),
                        stringify!($data),
                        stringify!($state),
                        vm_state.mem[$data]
                    );
                    */
                }
            };
        }

        let input = &mut context.0;

        #[cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]
        let input = CRLFtoLF(input); // Wrap input to replace CRLF to LF

        let mut in_stream = input.bytes();

        macro_rules! handle_input {
            ($addr:expr) => {
                if $addr == KBSR {
                    if let Some(result) = in_stream.next() {
                        vm_state.mem[KBSR] |= 0b1000_0000_0000_0000;
                        vm_state.mem[KBDR] = u16::from(result.unwrap());
                    }
                }
            };
        }

        macro_rules! handle_output {
            ($addr:expr) => {
                if $addr == DDR {
                    context.1.write_all(&[vm_state.mem[DDR] as u8])?;
                    vm_state.mem[DSR] |= 0b1000_0000_0000_0000;
                }
            };
        }

        #[cfg(feature = "instruction-trace")]
        eprintln!("[DEBUG] {:?}", instruction);

        match instruction {
            Instruction::ADD { dst, src1, src2 } => {
                reg!(dst) = reg!(src1).wrapping_add(reg!(src2));
                vm_state.update_condition(dst as usize);
            }
            Instruction::ADDi { dst, src, immd } => {
                reg!(dst) = reg!(src).wrapping_add(immd);
                vm_state.update_condition(dst as usize);
            }
            Instruction::AND { dst, src1, src2 } => {
                reg!(dst) = reg!(src1) & reg!(src2);
                vm_state.update_condition(dst as usize);
            }
            Instruction::ANDi { dst, src, immd } => {
                reg!(dst) = reg!(src) & immd;
                vm_state.update_condition(dst as usize);
            }
            Instruction::BR { cond, offset } => {
                if cond.satisfies(&vm_state.condition) {
                    vm_state.pc = vm_state.pc.wrapping_add(offset as u16);
                }
            }
            Instruction::JMP { base } => {
                vm_state.pc = reg!(base) as u16;
            }
            Instruction::JSR { offset } => {
                reg!(7) = vm_state.pc as i16;
                vm_state.pc = vm_state.pc.wrapping_add(offset as u16);
            }
            Instruction::JSRR { base } => {
                reg!(7) = vm_state.pc as i16;
                vm_state.pc = reg!(base) as u16;
            }
            Instruction::LD { dst, offset } => {
                let addr = (vm_state.pc.wrapping_add(offset as u16)) as usize;
                handle_input!(addr);

                reg!(dst) = vm_state.mem[addr] as i16;
                vm_state.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LDI { dst, offset } => {
                let addr =
                    vm_state.mem[(vm_state.pc.wrapping_add(offset as u16)) as usize] as usize;
                handle_input!(addr);

                reg!(dst) = vm_state.mem[addr] as i16;
                vm_state.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LDR { dst, base, offset } => {
                let addr = (reg!(base) as u16).wrapping_add(offset as u16) as usize;
                handle_input!(addr);

                reg!(dst) = vm_state.mem[addr] as i16;
                vm_state.update_condition(dst as usize);
                zero_if_eq!(addr, KBDR, KBSR);
            }
            Instruction::LEA { dst, offset } => {
                reg!(dst) = (vm_state.pc as i16).wrapping_add(offset);
                vm_state.update_condition(dst as usize);
            }
            Instruction::NOT { dst, src } => {
                reg!(dst) = !reg!(src);
                vm_state.update_condition(dst as usize);
            }
            Instruction::RTI => {
                context.1.write_fmt(format_args!(
                    "*** lc3-rs notification ***
lc3-rs does not support interrupts, but RTI instruction is being executed from address x{:04X}.
Please check your program if this is not intended.
*** End lc3-rs notification ***",
                    vm_state.pc - 1
                ))?;
            }
            Instruction::ST { src, offset } => {
                let addr = (vm_state.pc.wrapping_add(offset as u16)) as usize;
                vm_state.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                handle_output!(addr);
            }
            Instruction::STI { src, offset } => {
                let addr =
                    vm_state.mem[(vm_state.pc.wrapping_add(offset as u16)) as usize] as usize;
                vm_state.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                handle_output!(addr);
            }
            Instruction::STR { src, base, offset } => {
                let addr = (reg!(base) as u16).wrapping_add(offset as u16) as usize;
                vm_state.mem[addr] = reg!(src) as u16;
                zero_if_eq!(addr, DDR, DSR);

                handle_output!(addr);
            }
            Instruction::RESERVED => {
                context.1.write_fmt(format_args!(
                    "*** lc3-rs notification ***
A RESERVED instruction(0b1101) is being executed from address x{:04X}.
Please check your program if this is not intended.
*** End lc3-rs notification ***",
                    vm_state.pc - 1
                ))?;
            }
            Instruction::TRAP { vect } => {
                reg!(7) = vm_state.pc as i16;
                vm_state.pc = vm_state.mem[(vect as u16) as usize];
            }
        }
        Ok(())
    }
}
