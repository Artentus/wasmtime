//! A32 ISA definitions: immediate constants.

use std::fmt::{Display, Formatter, Result};

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Imm15(i16);

impl Imm15 {
    pub const ZERO: Self = Self(0);

    pub fn new(val: i64) -> Option<Self> {
        const MIN: i64 = -(1 << 14);
        const MAX: i64 = (1 << 14) - 1;

        if (val >= MIN) && (val <= MAX) {
            Some(Self(val as i16))
        } else {
            None
        }
    }

    pub fn bits(&self) -> u32 {
        (self.0 as u32) & 0x0000_7fff
    }
}

impl Display for Imm15 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Imm22(i32);

impl Imm22 {
    pub const ZERO: Self = Self(0);

    pub fn new(val: i64) -> Option<Self> {
        const MIN: i64 = -(1 << 21);
        const MAX: i64 = (1 << 21) - 1;

        if (val >= MIN) && (val <= MAX) && ((val & 0x3) == 0) {
            Some(Self(val as i32))
        } else {
            None
        }
    }

    pub fn bits(&self) -> u32 {
        (self.0 as u32) & 0x003f_ffff
    }
}

impl Display for Imm22 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct UImm20(i32);

impl UImm20 {
    pub const ZERO: Self = Self(0);

    pub fn new(val: i64) -> Option<Self> {
        const MIN: i64 = -(1 << 31);
        const MAX: i64 = (1 << 31) - 1;

        if (val >= MIN) && (val <= MAX) && ((val & 0xfff) == 0) {
            Some(Self(val as i32))
        } else {
            None
        }
    }

    pub fn bits(&self) -> u32 {
        (self.0 as u32) & 0xffff_f000
    }
}

impl Display for UImm20 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Display::fmt(&self.0, f)
    }
}

pub enum ImmPair {
    Lower(Imm15),
    Upper(UImm20),
    Pair(Imm15, UImm20),
}

pub fn gen_imm_pair(val: i32) -> ImmPair {
    if let Some(imm15) = Imm15::new(val as i64) {
        ImmPair::Lower(imm15)
    } else if let Some(uimm20) = UImm20::new(val as i64) {
        ImmPair::Upper(uimm20)
    } else {
        let imm15 = Imm15::new((val & 0x0000_0fff) as i64).unwrap();
        let uimm20 = UImm20::new((val & (0xffff_f000u32 as i32)) as i64).unwrap();
        ImmPair::Pair(imm15, uimm20)
    }
}
