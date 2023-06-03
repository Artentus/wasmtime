//! Implementation of a standard ARM ABI.

use crate::ir;
use crate::ir::types::*;
use crate::ir::Signature;
use crate::isa;
use crate::isa::arm::{inst::*, settings as arm_settings};
use crate::machinst::*;
use crate::settings;
use crate::CodegenResult;
use alloc::vec::Vec;
use regalloc2::PRegSet;
use smallvec::SmallVec;

/// Support for the ARM ABI from the callee side (within a function body).
pub(crate) type ArmCallee = Callee<ArmMachineDeps>;

/// Support for the ARM ABI from the caller side (at a callsite).
pub(crate) type ArmCallSite = CallSite<ArmMachineDeps>;

/// This is the limit for the size of argument and return-value areas on the
/// stack. We place a reasonable limit here to avoid integer overflow issues
/// with 32-bit arithmetic: for now, 128 MB.
static STACK_ARG_RET_SIZE_LIMIT: u32 = 128 * 1024 * 1024;

impl Into<AMode> for StackAMode {
    fn into(self) -> AMode {
        match self {
            StackAMode::FPOffset(off, ty) => AMode::FPOffset { off, ty },
            StackAMode::NominalSPOffset(off, ty) => AMode::NominalSPOffset { off, ty },
            StackAMode::SPOffset(off, ty) => AMode::SPOffset { off, ty },
        }
    }
}

/// ARM-specific ABI behavior. This struct just serves as an implementation
/// point for the trait; it is never actually instantiated.
pub struct ArmMachineDeps;

impl IsaFlags for arm_settings::Flags {
    fn is_forward_edge_cfi_enabled(&self) -> bool {
        false
    }
}

impl ABIMachineSpec for ArmMachineDeps {
    type I = Inst;
    type F = arm_settings::Flags;

    fn word_bits() -> u32 {
        todo!()
    }

    fn stack_align(call_conv: isa::CallConv) -> u32 {
        todo!()
    }

    fn compute_arg_locs<'a, I>(
        call_conv: isa::CallConv,
        flags: &settings::Flags,
        params: I,
        args_or_rets: ArgsOrRets,
        add_ret_area_ptr: bool,
        args: ArgsAccumulator<'_>,
    ) -> CodegenResult<(u32, Option<usize>)>
    where
        I: IntoIterator<Item = &'a ir::AbiParam>,
    {
        todo!()
    }

    fn fp_to_arg_offset(call_conv: isa::CallConv, flags: &settings::Flags) -> i64 {
        todo!()
    }

    fn gen_load_stack(mem: StackAMode, into_reg: Writable<Reg>, ty: Type) -> Self::I {
        todo!()
    }

    fn gen_store_stack(mem: StackAMode, from_reg: Reg, ty: Type) -> Self::I {
        todo!()
    }

    fn gen_move(to_reg: Writable<Reg>, from_reg: Reg, ty: Type) -> Self::I {
        todo!()
    }

    fn gen_extend(
        to_reg: Writable<Reg>,
        from_reg: Reg,
        is_signed: bool,
        from_bits: u8,
        to_bits: u8,
    ) -> Self::I {
        todo!()
    }

    fn gen_args(isa_flags: &Self::F, args: Vec<ArgPair>) -> Self::I {
        todo!()
    }

    fn gen_ret(
        setup_frame: bool,
        isa_flags: &Self::F,
        rets: Vec<RetPair>,
        stack_bytes_to_pop: u32,
    ) -> Self::I {
        todo!()
    }

    fn gen_add_imm(into_reg: Writable<Reg>, from_reg: Reg, imm: u32) -> SmallInstVec<Self::I> {
        todo!()
    }

    fn gen_stack_lower_bound_trap(limit_reg: Reg) -> SmallInstVec<Self::I> {
        todo!()
    }

    fn gen_get_stack_addr(mem: StackAMode, into_reg: Writable<Reg>, ty: Type) -> Self::I {
        todo!()
    }

    fn get_stacklimit_reg() -> Reg {
        todo!()
    }

    fn gen_load_base_offset(into_reg: Writable<Reg>, base: Reg, offset: i32, ty: Type) -> Self::I {
        todo!()
    }

    fn gen_store_base_offset(base: Reg, offset: i32, from_reg: Reg, ty: Type) -> Self::I {
        todo!()
    }

    fn gen_sp_reg_adjust(amount: i32) -> SmallInstVec<Self::I> {
        todo!()
    }

    fn gen_nominal_sp_adj(amount: i32) -> Self::I {
        todo!()
    }

    fn gen_prologue_frame_setup(flags: &settings::Flags) -> SmallInstVec<Self::I> {
        todo!()
    }

    fn gen_epilogue_frame_restore(flags: &settings::Flags) -> SmallInstVec<Self::I> {
        todo!()
    }

    fn gen_probestack(insts: &mut SmallInstVec<Self::I>, frame_size: u32) {
        todo!()
    }

    fn gen_inline_probestack(insts: &mut SmallInstVec<Self::I>, frame_size: u32, guard_size: u32) {
        todo!()
    }

    fn get_clobbered_callee_saves(
        call_conv: isa::CallConv,
        flags: &settings::Flags,
        sig: &Signature,
        regs: &[Writable<RealReg>],
    ) -> Vec<Writable<RealReg>> {
        todo!()
    }

    fn is_frame_setup_needed(
        is_leaf: bool,
        stack_args_size: u32,
        num_clobbered_callee_saves: usize,
        fixed_frame_storage_size: u32,
    ) -> bool {
        todo!()
    }

    fn gen_clobber_save(
        call_conv: isa::CallConv,
        setup_frame: bool,
        flags: &settings::Flags,
        clobbered_callee_saves: &[Writable<RealReg>],
        fixed_frame_storage_size: u32,
        outgoing_args_size: u32,
    ) -> (u64, SmallVec<[Self::I; 16]>) {
        todo!()
    }

    fn gen_clobber_restore(
        call_conv: isa::CallConv,
        sig: &Signature,
        flags: &settings::Flags,
        clobbers: &[Writable<RealReg>],
        fixed_frame_storage_size: u32,
        outgoing_args_size: u32,
    ) -> SmallVec<[Self::I; 16]> {
        todo!()
    }

    fn gen_call(
        dest: &CallDest,
        uses: CallArgList,
        defs: CallRetList,
        clobbers: PRegSet,
        opcode: ir::Opcode,
        tmp: Writable<Reg>,
        callee_conv: isa::CallConv,
        caller_conv: isa::CallConv,
    ) -> SmallVec<[Self::I; 2]> {
        todo!()
    }

    fn gen_memcpy<F: FnMut(Type) -> Writable<Reg>>(
        call_conv: isa::CallConv,
        dst: Reg,
        src: Reg,
        size: usize,
        alloc_tmp: F,
    ) -> SmallVec<[Self::I; 8]> {
        todo!()
    }

    fn get_number_of_spillslots_for_value(
        rc: RegClass,
        target_vector_bytes: u32,
        isa_flags: &Self::F,
    ) -> u32 {
        todo!()
    }

    fn get_virtual_sp_offset_from_state(s: &<Self::I as MachInstEmit>::State) -> i64 {
        todo!()
    }

    fn get_nominal_sp_to_fp(s: &<Self::I as MachInstEmit>::State) -> i64 {
        todo!()
    }

    fn get_regs_clobbered_by_call(call_conv_of_callee: isa::CallConv) -> PRegSet {
        todo!()
    }

    fn get_ext_mode(
        call_conv: isa::CallConv,
        specified: ir::ArgumentExtension,
    ) -> ir::ArgumentExtension {
        todo!()
    }
}
