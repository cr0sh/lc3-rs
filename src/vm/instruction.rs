#![allow(dead_code)]

#[inline]
fn sign_extend(x: i16, b: i16) -> i16 {
    ((x & ((1 << b) - 1)) ^ (1 << (b - 1))) - (1 << (b - 1))
}

macro_rules! extract_bits {
    ($data:ident[$offset:expr]) => {
        (($data >> $offset) & 1) as i16
    };
    ($data:ident[$start:expr; $end:expr]) => {
        (((1 << ($start - $end + 1)) - 1) & ($data >> $end)) as i16
    };
    (@extend $data:ident[$start:expr; $end:expr]) => {
        sign_extend(
            (((1 << ($start - $end + 1)) - 1) & ($data >> $end)) as i16,
            $start - $end + 1,
        )
    };
}

/// Condition code for LC-3.
/// Because the original LC-3 machine defines each condition codes
/// as separated bits of PSR, we don't define it as enum,
/// but struct with three boolean values.
#[derive(Clone, Debug, PartialEq)]
pub struct Condition {
    pub n: bool,
    pub z: bool,
    pub p: bool,
}

impl Condition {
    pub fn satisfies(&self, machine_cond: &Condition) -> bool {
        (self.n && machine_cond.n) || (self.z && machine_cond.z) || (self.p && machine_cond.p)
    }
}

impl Default for Condition {
    fn default() -> Condition {
        Condition {
            n: true,
            z: false,
            p: false,
        }
    }
}

impl Eq for Condition {}

/// A single LC-3 instruction.
/// Except condition codes and is_immd values, all fields are set to
/// i16 type for convenience.
#[derive(Debug, PartialEq)]
pub enum Instruction {
    ADD { dst: i16, src1: i16, src2: i16 },
    ADDi { dst: i16, src: i16, immd: i16 },
    AND { dst: i16, src1: i16, src2: i16 },
    ANDi { dst: i16, src: i16, immd: i16 },
    BR { cond: Condition, offset: i16 },
    JMP { base: i16 },
    JSR { offset: i16 },
    JSRR { base: i16 },
    LD { dst: i16, offset: i16 },
    LDI { dst: i16, offset: i16 },
    LDR { dst: i16, base: i16, offset: i16 },
    LEA { dst: i16, offset: i16 },
    NOT { dst: i16, src: i16 },
    RTI,
    ST { src: i16, offset: i16 },
    STI { src: i16, offset: i16 },
    STR { src: i16, base: i16, offset: i16 },
    RESERVED,
    TRAP { vect: i16 },
}

impl Instruction {
    /// Converts a single u16 value to LC-3 instruction.
    /// Note that for some instructions that can be interpreted
    /// in multiple types (e.g. JSR/JSRR), every field will be
    /// initialized to defined bit array slice values
    /// even if it won't be used.
    pub fn from_u16(data: u16) -> Instruction {
        match data >> 12 {
            0b0000 => Instruction::BR {
                cond: Condition {
                    n: extract_bits!(data[11]) > 0,
                    z: extract_bits!(data[10]) > 0,
                    p: extract_bits!(data[9]) > 0,
                },
                offset: extract_bits!(@extend data[8;0]),
            },
            0b0001 => {
                if extract_bits!(data[5]) > 0 {
                    Instruction::ADDi {
                        dst: extract_bits!(data[11;9]),
                        src: extract_bits!(data[8;6]),
                        immd: extract_bits!(@extend data[4;0]),
                    }
                } else {
                    Instruction::ADD {
                        dst: extract_bits!(data[11;9]),
                        src1: extract_bits!(data[8;6]),
                        src2: extract_bits!(data[2;0]),
                    }
                }
            }
            0b0010 => Instruction::LD {
                dst: extract_bits!(data[11;9]),
                offset: extract_bits!(@extend data[8;0]),
            },
            0b0011 => Instruction::ST {
                src: extract_bits!(data[11;9]),
                offset: extract_bits!(@extend data[8;0]),
            },
            0b0100 => {
                if extract_bits!(data[11]) > 0 {
                    Instruction::JSR {
                        offset: extract_bits!(@extend data[10;0]),
                    }
                } else {
                    Instruction::JSRR {
                        base: extract_bits!(data[8;6]),
                    }
                }
            }
            0b0101 => {
                if extract_bits!(data[5]) > 0 {
                    Instruction::ANDi {
                        dst: extract_bits!(data[11;9]),
                        src: extract_bits!(data[8;6]),
                        immd: extract_bits!(@extend data[4;0]),
                    }
                } else {
                    Instruction::AND {
                        dst: extract_bits!(data[11;9]),
                        src1: extract_bits!(data[8;6]),
                        src2: extract_bits!(data[2;0]),
                    }
                }
            }
            0b0110 => Instruction::LDR {
                dst: extract_bits!(data[11;9]),
                base: extract_bits!(data[8;6]),
                offset: extract_bits!(@extend data[5;0]),
            },
            0b0111 => Instruction::STR {
                src: extract_bits!(data[11;9]),
                base: extract_bits!(data[8;6]),
                offset: extract_bits!(@extend data[5;0]),
            },
            0b1000 => Instruction::RTI,
            0b1001 => Instruction::NOT {
                dst: extract_bits!(data[11;9]),
                src: extract_bits!(data[8;6]),
            },
            0b1010 => Instruction::LDI {
                dst: extract_bits!(data[11;9]),
                offset: extract_bits!(@extend data[8;0]),
            },
            0b1011 => Instruction::STI {
                src: extract_bits!(data[11;9]),
                offset: extract_bits!(@extend data[8;0]),
            },
            0b1100 => Instruction::JMP {
                base: extract_bits!(data[8;6]),
            },
            0b1101 => Instruction::RESERVED,
            0b1110 => Instruction::LEA {
                dst: extract_bits!(data[11;9]),
                offset: extract_bits!(@extend data[8;0]),
            },
            0b1111 => Instruction::TRAP {
                vect: extract_bits!(data[7;0]),
            },
            0b10000...0xFFFF => unreachable!(),
        }
    }
}

impl Eq for Instruction {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sign_extend() {
        assert_eq!(sign_extend(0b0000_0000_0000_0011 as i16, 2), -1);
        assert_eq!(sign_extend(0b0000_0000_0000_0111 as i16, 3), -1);
        assert_eq!(sign_extend(0b0000_0000_0000_0111 as i16, 4), 7);
        assert_eq!(sign_extend(0b0000_0000_0001_0111 as i16, 4), 7);
        assert_eq!(
            sign_extend(0b0000_0000_0001_0111 as i16, 5),
            0b1111_1111_1111_0111 as u16 as i16
        );
    }

    #[test]
    fn test_extract_bits() {
        let data: u16 = 0b0010_1101_0010_0011;
        assert_eq!(extract_bits!(data[0]), 1);
        assert_eq!(extract_bits!(data[3]), 0);
        assert_eq!(extract_bits!(data[0;0]), 1);
        assert_eq!(extract_bits!(data[1;0]), 3);
        assert_eq!(extract_bits!(data[16;12]), 2);
        assert_eq!(extract_bits!(@extend data[1;0]), -1);
        assert_eq!(
            extract_bits!(@extend data[5;1]),
            0b1111_0001 as u8 as i8 as i16 // TODO: It is too ugly...
        );
        assert_eq!(
            extract_bits!(@extend data[13;8]),
            0b1110_1101 as u8 as i8 as i16
        );
        assert_eq!(extract_bits!(@extend data[16;12]), 2);

        let data1: u16 = 0xF025;
        assert_eq!(extract_bits!(data1[7;0]), 37);
    }

    // TODO: Add more cases
    #[test]
    fn test_instruction_parse() {
        assert_eq!(
            Instruction::from_u16(0x1406),
            Instruction::ADD {
                src1: 0,
                src2: 6,
                dst: 2,
            }
        );
        assert_eq!(
            Instruction::from_u16(0xF020),
            Instruction::TRAP { vect: 32 }
        );
        assert_eq!(
            Instruction::from_u16(0x0402),
            Instruction::BR {
                cond: Condition {
                    n: false,
                    z: true,
                    p: false,
                },
                offset: 2,
            }
        );
    }

}
