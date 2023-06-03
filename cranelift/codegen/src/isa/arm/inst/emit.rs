//! ARM ISA: binary code emission.

use cranelift_control::ControlPlane;
use regalloc2::Allocation;

use crate::binemit::StackMap;
use crate::ir::RelSourceLoc;
use crate::isa::arm::inst::*;

/// State carried between emissions of a sequence of instructions.
#[derive(Default, Clone, Debug)]
pub struct EmitState {
    /// Addend to convert nominal-SP offsets to real-SP offsets at the current
    /// program point.
    pub(crate) virtual_sp_offset: i64,
    /// Offset of FP from nominal-SP.
    pub(crate) nominal_sp_to_fp: i64,
    /// Safepoint stack map for upcoming instruction, as provided to `pre_safepoint()`.
    stack_map: Option<StackMap>,
    /// Current source-code location corresponding to instruction to be emitted.
    cur_srcloc: RelSourceLoc,
    /// Only used during fuzz-testing. Otherwise, it is a zero-sized struct and
    /// optimized away at compiletime. See [cranelift_control].
    ctrl_plane: ControlPlane,
}

impl MachInstEmitState<Inst> for EmitState {
    fn new(abi: &Callee<ArmMachineDeps>, ctrl_plane: ControlPlane) -> Self {
        todo!()
    }

    fn ctrl_plane_mut(&mut self) -> &mut ControlPlane {
        todo!()
    }

    fn take_ctrl_plane(self) -> ControlPlane {
        todo!()
    }
}

/// Constant state used during function compilation.
pub struct EmitInfo(settings::Flags);

impl EmitInfo {
    /// Create a constant state for emission of instructions.
    pub fn new(flags: settings::Flags) -> Self {
        Self(flags)
    }
}

impl MachInstEmit for Inst {
    type State = EmitState;
    type Info = EmitInfo;

    fn emit(
        &self,
        allocs: &[Allocation],
        code: &mut MachBuffer<Self>,
        info: &Self::Info,
        state: &mut Self::State,
    ) {
        todo!()
    }

    fn pretty_print_inst(
        &self,
        allocs: &[Allocation],
        state: &mut Self::State,
    ) -> alloc::string::String {
        todo!()
    }
}
