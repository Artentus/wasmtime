//! ISLE integration glue code for ARM lowering.

// Pull in the ISLE generated code.
pub mod generated_code;
use generated_code::Context;

// Types that the generated ISLE code uses via `use super::*`.
use super::{
    AMode, CallIndInfo, CallInfo, FloatCC, Inst as MInst, IntCC, JTSequenceInfo, MachLabel, Opcode,
};
use crate::ir::condcodes;
use crate::isa::arm::ArmBackend;
use crate::machinst::valueregs;
use crate::machinst::{isle::*, InputSourceInst};
use crate::{
    ir::{
        immediates::*, types::*, BlockCall, ExternalName, Inst, InstructionData, MemFlags,
        TrapCode, Value, ValueList,
    },
    isa::arm::abi::ArmCallSite,
    machinst::{abi::ArgPair, InstOutput, Lower, MachInst, VCodeConstant, VCodeConstantData},
};
use crate::{isle_common_prelude_methods, isle_lower_prelude_methods};
use regalloc2::PReg;
use std::boxed::Box;
use std::convert::TryFrom;
use std::vec::Vec;

type BoxCallInfo = Box<CallInfo>;
type BoxCallIndInfo = Box<CallIndInfo>;
type VecMachLabel = Vec<MachLabel>;
type BoxJTSequenceInfo = Box<JTSequenceInfo>;
type BoxExternalName = Box<ExternalName>;
type VecArgPair = Vec<ArgPair>;

/// The main entry point for lowering with ISLE.
pub(crate) fn lower(
    lower_ctx: &mut Lower<MInst>,
    backend: &ArmBackend,
    inst: Inst,
) -> Option<InstOutput> {
    // TODO: reuse the ISLE context across lowerings so we can reuse its
    // internal heap allocations.
    let mut isle_ctx = IsleContext { lower_ctx, backend };
    generated_code::constructor_lower(&mut isle_ctx, inst)
}

pub(crate) fn lower_branch(
    lower_ctx: &mut Lower<MInst>,
    backend: &ArmBackend,
    branch: Inst,
    targets: &[MachLabel],
) -> Option<()> {
    // TODO: reuse the ISLE context across lowerings so we can reuse its
    // internal heap allocations.
    let mut isle_ctx = IsleContext { lower_ctx, backend };
    generated_code::constructor_lower_branch(&mut isle_ctx, branch, &targets.to_vec())
}

impl IsleContext<'_, '_, MInst, ArmBackend> {
    isle_prelude_method_helpers!(ArmCallSite);
}

impl Context for IsleContext<'_, '_, MInst, ArmBackend> {
    isle_lower_prelude_methods!();
    isle_prelude_caller_methods!(crate::isa::arm::abi::ArmMachineDeps, ArmCallSite);

    fn emit(&mut self, inst: &MInst) -> Unit {
        self.lower_ctx.emit(inst.clone());
    }

    fn placeholder(&mut self) -> Unit {}
}
