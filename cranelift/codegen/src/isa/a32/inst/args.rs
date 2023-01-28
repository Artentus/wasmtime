//! A32 definitions: instruction arguments.

// Some variants are never constructed, but we still want them as options in the future.
#![allow(dead_code)]
use super::*;

use crate::isa::a32::inst::reg_name;

/// An addressing mode specified for a load/store operation.
#[derive(Clone, Debug, Copy)]
pub enum AMode {
    /// Offset from an arbitrary register.
    RegOffset(Reg, i32),
    /// Offset from the stack pointer.
    SPOffset(i32),
    /// Offset from the frame pointer.
    FPOffset(i32),
    /// Offset from the nominal stack pointer.
    NominalSPOffset(i32),
}

impl AMode {
    pub(crate) fn base(&self) -> Option<Reg> {
        match self {
            &AMode::RegOffset(reg, _) => Some(reg),
            _ => None,
        }
    }

    pub(crate) fn pbase(&self, allocs: &mut AllocationConsumer) -> Reg {
        match self {
            &AMode::RegOffset(reg, _) => allocs.next(reg),
            &AMode::SPOffset(_) => sp(),
            &AMode::FPOffset(_) => s12(),
            &AMode::NominalSPOffset(_) => sp(),
        }
    }

    pub(crate) fn pbase_name(&self, allocs: &mut AllocationConsumer) -> String {
        reg_name(self.pbase(allocs))
    }

    pub(crate) fn offset(&self, state: &EmitState) -> i32 {
        match self {
            &AMode::RegOffset(_, offset) => offset,
            &AMode::SPOffset(offset) => offset,
            &AMode::FPOffset(offset) => offset,
            &AMode::NominalSPOffset(offset) => offset + state.nominal_sp_offset,
        }
    }
}

impl From<StackAMode> for AMode {
    fn from(value: StackAMode) -> Self {
        match value {
            StackAMode::FPOffset(offset, _) => AMode::FPOffset(offset as i32),
            StackAMode::SPOffset(offset, _) => AMode::SPOffset(offset as i32),
            StackAMode::NominalSPOffset(offset, _) => AMode::NominalSPOffset(offset as i32),
        }
    }
}
