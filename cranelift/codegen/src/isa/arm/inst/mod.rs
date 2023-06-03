//! This module defines ARM-specific machine instruction types.

use crate::binemit::CodeOffset;
use crate::ir::{ExternalName, Opcode, Type};
use crate::isa::arm::abi::ArmMachineDeps;
use crate::isa::{CallConv, FunctionAlignment};
use crate::machinst::*;
use crate::machinst::{Reg, RegClass, Writable};
use crate::{settings, CodegenResult};
use alloc::vec::Vec;
use regalloc2::{PRegSet, VReg};
use smallvec::SmallVec;

pub(crate) mod regs;
pub(crate) use self::regs::*;
pub mod args;
pub use self::args::*;
pub mod emit;
pub(crate) use self::emit::*;

//=============================================================================
// Instructions (top level): definition

pub use crate::isa::arm::lower::isle::generated_code::{AMode, MInst as Inst};

/// Additional information for (direct) Call instructions, left out of line to lower the size of
/// the Inst enum.
#[derive(Clone, Debug)]
pub struct CallInfo {
    /// Call destination.
    pub dest: ExternalName,
    /// Arguments to the call instruction.
    pub uses: CallArgList,
    /// Return values from the call instruction.
    pub defs: CallRetList,
    /// Clobbers register set.
    pub clobbers: PRegSet,
    /// Instruction opcode.
    pub opcode: Opcode,
    /// Caller calling convention.
    pub caller_callconv: CallConv,
    /// Callee calling convention.
    pub callee_callconv: CallConv,
}

/// Additional information for CallInd instructions, left out of line to lower the size of the Inst
/// enum.
#[derive(Clone, Debug)]
pub struct CallIndInfo {
    /// Function pointer for indirect call.
    pub rn: Reg,
    /// Arguments to the call instruction.
    pub uses: SmallVec<[CallArgPair; 8]>,
    /// Return values from the call instruction.
    pub defs: SmallVec<[CallRetPair; 8]>,
    /// Clobbers register set.
    pub clobbers: PRegSet,
    /// Instruction opcode.
    pub opcode: Opcode,
    /// Caller calling convention.
    pub caller_callconv: CallConv,
    /// Callee calling convention.
    pub callee_callconv: CallConv,
}

/// Additional information for JTSequence instructions, left out of line to lower the size of the Inst
/// enum.
#[derive(Clone, Debug)]
pub struct JTSequenceInfo {
    /// Possible branch targets.
    pub targets: Vec<BranchTarget>,
    /// Default branch target.
    pub default_target: BranchTarget,
}

//=============================================================================
// Instructions: misc functions and external interface

impl MachInst for Inst {
    type ABIMachineSpec = ArmMachineDeps;
    type LabelUse = LabelUse;

    const TRAP_OPCODE: &'static [u8] = todo!();

    fn get_operands<F: Fn(VReg) -> VReg>(&self, collector: &mut OperandCollector<'_, F>) {
        todo!()
    }

    fn is_move(&self) -> Option<(Writable<Reg>, Reg)> {
        todo!()
    }

    fn is_term(&self) -> MachTerminator {
        todo!()
    }

    fn is_trap(&self) -> bool {
        todo!()
    }

    fn is_args(&self) -> bool {
        todo!()
    }

    fn is_included_in_clobbers(&self) -> bool {
        todo!()
    }

    fn gen_move(to_reg: Writable<Reg>, from_reg: Reg, ty: Type) -> Self {
        todo!()
    }

    fn gen_dummy_use(reg: Reg) -> Self {
        todo!()
    }

    fn rc_for_type(ty: Type) -> CodegenResult<(&'static [RegClass], &'static [Type])> {
        todo!()
    }

    fn canonical_type_for_rc(rc: RegClass) -> Type {
        todo!()
    }

    fn gen_jump(target: MachLabel) -> Self {
        todo!()
    }

    fn gen_nop(preferred_size: usize) -> Self {
        todo!()
    }

    fn worst_case_size() -> CodeOffset {
        todo!()
    }

    fn ref_type_regclass(_flags: &settings::Flags) -> RegClass {
        todo!()
    }

    fn is_safepoint(&self) -> bool {
        todo!()
    }

    fn function_alignment() -> FunctionAlignment {
        todo!()
    }
}

//=============================================================================
// Label fixups and jump veneers.

/// Different forms of label references for different instruction formats.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LabelUse {}

impl MachInstLabelUse for LabelUse {
    const ALIGN: CodeOffset = 4;

    fn max_pos_range(self) -> CodeOffset {
        todo!()
    }

    fn max_neg_range(self) -> CodeOffset {
        todo!()
    }

    fn patch_size(self) -> CodeOffset {
        todo!()
    }

    fn patch(self, buffer: &mut [u8], use_offset: CodeOffset, label_offset: CodeOffset) {
        todo!()
    }

    fn supports_veneer(self) -> bool {
        todo!()
    }

    fn veneer_size(self) -> CodeOffset {
        todo!()
    }

    fn generate_veneer(self, buffer: &mut [u8], veneer_offset: CodeOffset) -> (CodeOffset, Self) {
        todo!()
    }

    fn from_reloc(reloc: crate::binemit::Reloc, addend: crate::binemit::Addend) -> Option<Self> {
        todo!()
    }
}
