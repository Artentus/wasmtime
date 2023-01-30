//! Implementation of a standard A32 ABI.

use crate::ir;
use crate::ir::types::*;
use crate::ir::ExternalName;
use crate::isa;
use crate::isa::a32::inst::*;
use crate::machinst::*;
use crate::ir::types::I8;
use crate::ir::LibCall;
use crate::ir::Signature;
use crate::isa::a32::settings::Flags as A32Flags;
use crate::settings;
use crate::CodegenError;
use crate::CodegenResult;
use alloc::boxed::Box;
use alloc::vec::Vec;
use regalloc2::PRegSet;
use smallvec::{smallvec, SmallVec};

/// Support for the A32 ABI from the callee side (within a function body).
pub(crate) type A32Callee = Callee<A32MachineDeps>;

/// Support for the A32 ABI from the caller side (at a callsite).
pub(crate) type A32ABICaller = Caller<A32MachineDeps>;

/// This is the limit for the size of argument and return-value areas on the
/// stack. We place a reasonable limit here to avoid integer overflow issues
/// with 32-bit arithmetic: for now, 128 MB.
static STACK_ARG_RET_SIZE_LIMIT: u32 = 128 * 1024 * 1024;

impl IsaFlags for A32Flags {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegSaveMode {
    None,
    Caller,
    Callee,
}

const REG_SAVE_MODE: [RegSaveMode; 32] = {
    use RegSaveMode::*;
    [
        None, Caller, Callee, // zero, ra, sp
        Caller, Caller, Caller, Caller, Caller, Caller, Caller, Caller, // a0-a7
        Caller, Caller, Caller, Caller, Caller, Caller, Caller, Caller, // t0-t7
        Callee, Callee, Callee, Callee, Callee, Callee, Callee, Callee, // s0-s7
        Callee, Callee, Callee, Callee, Callee, // s8-s12
    ]
};

#[inline]
fn is_callee_saved(reg: RealReg) -> bool {
    REG_SAVE_MODE[reg.hw_enc() as usize] == RegSaveMode::Callee
}

#[inline]
fn compute_clobber_size(clobbers: &[Writable<RealReg>]) -> u32 {
    (clobbers.len() as u32) * 4
}

/// A32-specific ABI behavior. This struct just serves as an implementation
/// point for the trait; it is never actually instantiated.
pub struct A32MachineDeps;

impl ABIMachineSpec for A32MachineDeps {
    type I = MInst;
    type F = A32Flags;

    fn word_bits() -> u32 {
        32
    }

    fn stack_align(_call_conv: isa::CallConv) -> u32 {
        4
    }

    fn compute_arg_locs<'a, I>(
        call_conv: isa::CallConv,
        _flags: &settings::Flags,
        params: I,
        args_or_rets: ArgsOrRets,
        add_ret_area_ptr: bool,
        mut args: ArgsAccumulator<'_>,
    ) -> CodegenResult<(u32, Option<usize>)>
    where
        I: IntoIterator<Item = &'a ir::AbiParam> {
        // All registers that can be used as parameters or return values
        let regs: &[regalloc2::PReg] = match args_or_rets {
            ArgsOrRets::Args => &[P_A0, P_A1, P_A2, P_A3, P_A4, P_A5, P_A6, P_A7],
            ArgsOrRets::Rets if call_conv.extends_wasmtime() => &[P_A0],
            ArgsOrRets::Rets => &[P_A0, P_A1, P_A2, P_A3],
        };
        let mut regs = regs.iter().copied();

        // Stack space
        let mut next_stack: u32 = 0;

        for param in params {
            if let ir::ArgumentPurpose::StructArgument(size) = param.purpose {
                assert!((size % 8) == 0, "StructArgument size is not properly aligned");

                args.push(ABIArg::StructArg {
                    pointer: None,
                    offset: next_stack as i64,
                    size: size as u64,
                    purpose: param.purpose,
                });

                next_stack += size;
                continue;
            }

            // Find the register(s) used to store a value of this type
            let (_, reg_tys) = MInst::rc_for_type(param.value_type)?;

            let mut slots = ABIArgSlotVec::new();
            for reg_ty in reg_tys.iter().copied() {
                if let Some(reg) = regs.next() {
                    slots.push(ABIArgSlot::Reg {
                        reg: reg.into(),
                        ty: reg_ty,
                        extension: param.extension,
                    });
                } else {
                    // Compute size. For the wasmtime ABI it differs from native
                    // ABIs in how multiple values are returned, so we take a
                    // leaf out of arm64's book by not rounding everything up to
                    // 4 bytes. For all ABI arguments, and other ABI returns,
                    // though, each slot takes a minimum of 4 bytes.
                    //
                    // Note that in all cases 16-byte stack alignment happens
                    // separately after all args.
                    let size = reg_ty.bits() / 8;
                    let size = if (args_or_rets == ArgsOrRets::Rets) && call_conv.extends_wasmtime() {
                        size
                    } else {
                        std::cmp::max(size, 4)
                    };
                    assert!(size.is_power_of_two());

                    next_stack = align_to(next_stack, size);
                    slots.push(ABIArgSlot::Stack {
                        offset: next_stack as i64,
                        ty: reg_ty,
                        extension: param.extension,
                    });
                    next_stack += size;
                }
            }

            args.push(ABIArg::Slots {
                slots,
                purpose: param.purpose,
            });
        }

        let pos: Option<usize> = if add_ret_area_ptr {
            assert_eq!(args_or_rets, ArgsOrRets::Args);

            if let Some(reg) = regs.next() {
                args.push(ABIArg::reg(
                    reg.into(),
                    I32,
                    ir::ArgumentExtension::None,
                    ir::ArgumentPurpose::Normal,
                ));
            } else {
                args.push(ABIArg::stack(
                    next_stack as i64,
                    I32,
                    ir::ArgumentExtension::None,
                    ir::ArgumentPurpose::Normal,
                ));
                next_stack += 4;
            }

            Some(args.args().len() - 1)
        } else {
            None
        };

        next_stack = align_to(next_stack, Self::stack_align(call_conv));

        // To avoid overflow issues, limit the arg/return size to something
        // reasonable -- here, 128 MB.
        if next_stack > STACK_ARG_RET_SIZE_LIMIT {
            return Err(CodegenError::ImplLimitExceeded);
        }

        CodegenResult::Ok((next_stack, pos))
    }

    fn fp_to_arg_offset(_call_conv: isa::CallConv, _flags: &settings::Flags) -> i64 {
        8
    }

    fn gen_load_stack(mode: StackAMode, into_reg: Writable<Reg>, _ty: Type) -> Self::I {
        MInst::Load {
            op: LoadOP::Ld32,
            rd: into_reg,
            mode: mode.into(),
        }
    }

    fn gen_store_stack(mode: StackAMode, from_reg: Reg, _ty: Type) -> Self::I {
        MInst::Store {
            op: StoreOP::St32,
            rs: from_reg,
            mode: mode.into(),
        }
    }

    fn gen_move(to_reg: Writable<Reg>, from_reg: Reg, _ty: Type) -> Self::I {
        MInst::Move { rd: to_reg, rs: from_reg }
    }

    fn gen_extend(
        to_reg: Writable<Reg>,
        from_reg: Reg,
        signed: bool,
        from_bits: u8,
        to_bits: u8,
    ) -> Self::I {
        assert!(to_bits == 32);
        assert!(from_bits < to_bits);

        MInst::Extend {
            rd: to_reg,
            rs: from_reg,
            signed,
            from_bits,
            to_bits,
        }
    }

    fn gen_args(_isa_flags: &Self::F, args: Vec<ArgPair>) -> Self::I {
        MInst::Args { args }
    }

    fn gen_ret(_setup_frame: bool, _isa_flags: &Self::F, rets: Vec<RetPair>) -> Self::I {
        MInst::Ret { rets }
    }

    fn gen_add_imm(into_reg: Writable<Reg>, from_reg: Reg, imm: u32) -> SmallInstVec<Self::I> {
        if let Some(imm) = Imm15::new((imm as i32) as i64) {
            smallvec![MInst::AluRegImm { op: AluOP::Add, rd: into_reg, rs: from_reg, imm }]
        } else {
            let mut insts = MInst::load_imm32(t7_w(), imm as i32);
            insts.push(MInst::AluRegReg { op: AluOP::Add, rd: into_reg, rs1: from_reg, rs2: t7() });
            insts
        }
    }

    fn gen_stack_lower_bound_trap(_limit_reg: Reg) -> SmallInstVec<Self::I> {
        unimplemented!("stack probing is not supported");
    }

    fn gen_get_stack_addr(mode: StackAMode, into_reg: Writable<Reg>, _ty: Type) -> Self::I {
        MInst::LoadAddr {
            rd: into_reg,
            mode: mode.into(),
        }
    }

    fn get_stacklimit_reg() -> Reg {
        unimplemented!("stack probing is not supported");
    }

    fn gen_load_base_offset(into_reg: Writable<Reg>, base: Reg, offset: i32, ty: Type) -> Self::I {
        let op = match ty {
            I8 => LoadOP::Ld8,
            I16 => LoadOP::Ld16,
            I32 | R32 => LoadOP::Ld32,
            _ => unreachable!("invalid load type")
        };

        MInst::Load { op, rd: into_reg, mode: AMode::RegOffset(base, offset) }
    }

    fn gen_store_base_offset(base: Reg, offset: i32, from_reg: Reg, ty: Type) -> Self::I {
        let op = match ty {
            I8 => StoreOP::St8,
            I16 => StoreOP::St16,
            I32 | R32 => StoreOP::St32,
            _ => unreachable!("invalid load type")
        };

        MInst::Store { op, rs: from_reg, mode: AMode::RegOffset(base, offset) }
    }

    fn gen_sp_reg_adjust(amount: i32) -> SmallInstVec<Self::I> {
        if amount == 0 {
            smallvec![]
        } else {
            smallvec![MInst::SPAdj { amount }]
        }
    }

    fn gen_nominal_sp_adj(amount: i32) -> Self::I {
        MInst::NominalSPAdj { amount }
    }

    fn gen_prologue_frame_setup(_flags: &settings::Flags) -> SmallInstVec<Self::I> {
        // sub sp, sp, 8    ;; alloc stack space
        // st  [sp, 0], ra  ;; save ra
        // st  [sp, 4], s12 ;; save old fp
        // mov s12, sp      ;; set fp to sp

        let mut insts = SmallVec::new();
        insts.extend(Self::gen_sp_reg_adjust(-8));
        insts.push(Self::gen_store_stack(
            StackAMode::SPOffset(0, I32),
            ra(),
            I32,
        ));
        insts.push(Self::gen_store_stack(
            StackAMode::SPOffset(4, I32),
            s12(),
            I32,
        ));
        insts.push(MInst::Move {
            rd: s12_w(),
            rs: sp(),
        });
        insts
    }

    fn gen_epilogue_frame_restore(_flags: &settings::Flags) -> SmallInstVec<Self::I> {
        // ld  ra, [sp, 0]  ;; restore ra
        // ld  s12, [sp, 4] ;; restore old fp
        // add sp, sp, 8    ;; free stack space

        let mut insts = SmallVec::new();
        insts.push(Self::gen_load_stack(
            StackAMode::SPOffset(0, I32),
            ra_w(),
            I32,
        ));
        insts.push(Self::gen_load_stack(
            StackAMode::SPOffset(4, I32),
            s12_w(),
            I32,
        ));
        insts.extend(Self::gen_sp_reg_adjust(8));
        insts
    }

    fn gen_probestack(_insts: &mut SmallInstVec<Self::I>, _frame_size: u32) {
        unimplemented!("stack probing is not supported");
    }

    fn gen_inline_probestack(_insts: &mut SmallInstVec<Self::I>, _frame_size: u32, _guard_size: u32) {
        unimplemented!("stack probing is not supported");
    }

    fn get_clobbered_callee_saves(
        _call_conv: isa::CallConv,
        _flags: &settings::Flags,
        _sig: &Signature,
        regs: &[Writable<RealReg>],
    ) -> Vec<Writable<RealReg>> {
        let mut regs: Vec<Writable<RealReg>> = regs
            .iter()
            .cloned()
            .filter(|r| is_callee_saved(r.to_reg()))
            .collect();

        regs.sort();
        regs
    }

    fn is_frame_setup_needed(
        is_leaf: bool,
        stack_args_size: u32,
        num_clobbered_callee_saves: usize,
        fixed_frame_storage_size: u32,
    ) -> bool {
        !is_leaf
            // The function arguments that are passed on the stack are addressed
            // relative to the Frame Pointer.
            || stack_args_size > 0
            || num_clobbered_callee_saves > 0
        || fixed_frame_storage_size > 0
    }

    fn gen_clobber_save(
        _call_conv: isa::CallConv,
        _setup_frame: bool,
        _flags: &settings::Flags,
        clobbered_callee_saves: &[Writable<RealReg>],
        fixed_frame_storage_size: u32,
        _outgoing_args_size: u32,
    ) -> (u64, SmallVec<[Self::I; 16]>) {
        // Adjust the stack pointer downward for clobbers and the function fixed
        // frame (spillslots and storage slots).
        let clobbered_size = compute_clobber_size(&clobbered_callee_saves);
        let stack_size = align_to(fixed_frame_storage_size, 4) + clobbered_size;

        // Store each clobbered register in order at offsets from SP,
        // placing them above the fixed frame slots.
        let mut insts = SmallVec::new();
        if stack_size > 0 {
            let stack_offset = Imm15::new((stack_size as i32) as i64).expect("stack frame too big");
            insts.push(MInst::AluRegImm { op: AluOP::Sub, rd: sp_w(), rs: sp(), imm: stack_offset });

            let mut cur_offset = align_to(fixed_frame_storage_size, 4) as i64;
            for reg in clobbered_callee_saves {
                insts.push(Self::gen_store_stack(
                    StackAMode::SPOffset(cur_offset, I32),
                    real_reg_to_reg(reg.to_reg()),
                    I32,
                ));
                cur_offset += 4;
            }
        }

        (clobbered_size as u64, insts)
    }

    fn gen_clobber_restore(
        call_conv: isa::CallConv,
        sig: &Signature,
        flags: &settings::Flags,
        clobbers: &[Writable<RealReg>],
        fixed_frame_storage_size: u32,
        _outgoing_args_size: u32,
    ) -> SmallVec<[Self::I; 16]> {
        // Adjust the stack pointer downward for clobbers and the function fixed
        // frame (spillslots and storage slots).
        let clobbered_callee_saves = Self::get_clobbered_callee_saves(call_conv, flags, sig, clobbers);
        let clobbered_size = compute_clobber_size(&clobbered_callee_saves);
        let stack_size = align_to(fixed_frame_storage_size, 4) + clobbered_size;

        // Store each clobbered register in order at offsets from SP,
        // placing them above the fixed frame slots.
        let mut insts = SmallVec::new();
        if stack_size > 0 {
            let mut cur_offset = align_to(fixed_frame_storage_size, 4) as i64;
            for reg in clobbered_callee_saves {
                insts.push(Self::gen_load_stack(
                    StackAMode::SPOffset(cur_offset, I32),
                    Writable::from_reg(real_reg_to_reg(reg.to_reg())),
                    I32,
                ));
                cur_offset += 4;
            }

            let stack_offset = Imm15::new((stack_size as i32) as i64).expect("stack frame too big");
            insts.push(MInst::AluRegImm { op: AluOP::Add, rd: sp_w(), rs: sp(), imm: stack_offset });
        }

        insts
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
        let mut insts = SmallVec::new();
        match dest {
            CallDest::ExtName(name, RelocDistance::Near) => insts.push(MInst::Call {
                info: Box::new(CallInfo {
                    dest: name.clone(),
                    uses,
                    defs,
                    clobbers,
                    opcode,
                    caller_callconv: caller_conv,
                    callee_callconv: callee_conv,
                }),
            }),
            CallDest::ExtName(name, RelocDistance::Far) => {
                insts.push(MInst::LoadExtName {
                    rd: tmp,
                    name: Box::new(name.clone()),
                    offset: 0,
                });
                insts.push(MInst::CallInd {
                    info: Box::new(CallIndInfo {
                        rn: tmp.to_reg(),
                        uses,
                        defs,
                        clobbers,
                        opcode,
                        caller_callconv: caller_conv,
                        callee_callconv: callee_conv,
                    }),
                });
            }
            &CallDest::Reg(reg) => insts.push(MInst::CallInd {
                info: Box::new(CallIndInfo {
                    rn: reg,
                    uses,
                    defs,
                    clobbers,
                    opcode,
                    caller_callconv: caller_conv,
                    callee_callconv: callee_conv,
                }),
            }),
        }
        insts
    }

    fn gen_memcpy<F: FnMut(Type) -> Writable<Reg>>(
        call_conv: isa::CallConv,
        dst: Reg,
        src: Reg,
        size: usize,
        mut alloc_tmp: F,
    ) -> SmallVec<[Self::I; 8]> {
        let mut insts = SmallVec::new();

        let tmp = alloc_tmp(I32);
        insts.extend(MInst::load_imm32(tmp, size as i32).into_iter());

        insts.push(MInst::Call {
            info: Box::new(CallInfo {
                dest: ExternalName::LibCall(LibCall::Memcpy),
                uses: smallvec![
                    CallArgPair {
                        vreg: dst,
                        preg: a0()
                    },
                    CallArgPair {
                        vreg: src,
                        preg: a1()
                    },
                    CallArgPair {
                        vreg: tmp.to_reg(),
                        preg: a2()
                    }
                ],
                defs: smallvec![],
                clobbers: Self::get_regs_clobbered_by_call(call_conv),
                opcode: Opcode::Call,
                caller_callconv: call_conv,
                callee_callconv: call_conv,
            }),
        });

        insts
    }

    fn get_number_of_spillslots_for_value(rc: RegClass, _target_vector_bytes: u32) -> u32 {
        match rc {
            RegClass::Int => 1,
            RegClass::Float => 1,
        }
    }

    fn get_virtual_sp_offset_from_state(s: &<Self::I as MachInstEmit>::State) -> i64 {
        s.nominal_sp_offset as i64
    }

    fn get_nominal_sp_to_fp(s: &<Self::I as MachInstEmit>::State) -> i64 {
        s.nominal_sp_to_fp as i64
    }

    fn get_regs_clobbered_by_call(_call_conv_of_callee: isa::CallConv) -> PRegSet {
        let mut v = PRegSet::empty();
        for (i, mode) in REG_SAVE_MODE.iter().copied().enumerate() {
            if mode == RegSaveMode::Caller {
                v.add(p_reg(i));
            }
        }
        v
    }

    fn get_ext_mode(
        _call_conv: isa::CallConv,
        specified: ir::ArgumentExtension,
    ) -> ir::ArgumentExtension {
        specified
    }
}
