//! Lowering rules for ARM.

use crate::ir::condcodes::{FloatCC, IntCC};
use crate::ir::{Inst as IRInst, Opcode};
use crate::isa::arm::inst::*;
use crate::isa::arm::ArmBackend;
use crate::machinst::lower::*;
use crate::machinst::Reg;
use crate::machinst::*;

pub mod isle;

//=============================================================================
// Lowering-backend trait implementation.

impl LowerBackend for ArmBackend {
    type MInst = Inst;

    fn lower(&self, ctx: &mut Lower<Inst>, ir_inst: IRInst) -> Option<InstOutput> {
        isle::lower(ctx, self, ir_inst)
    }

    fn lower_branch(
        &self,
        ctx: &mut Lower<Inst>,
        ir_inst: IRInst,
        targets: &[MachLabel],
    ) -> Option<()> {
        isle::lower_branch(ctx, self, ir_inst, targets)
    }

    fn maybe_pinned_reg(&self) -> Option<Reg> {
        todo!()
    }
}
