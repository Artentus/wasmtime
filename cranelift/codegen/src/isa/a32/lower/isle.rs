//! ISLE integration glue code for A32 lowering.

// Pull in the ISLE generated code.
#[allow(unused)]
pub mod generated_code;
use generated_code::{Context, MInst};
use smallvec::smallvec;

use crate::{isle_common_prelude_methods, isle_lower_prelude_methods};
use crate::isa::a32::abi::A32ABICaller;
use crate::isa::a32::A32Backend;
use crate::isa::a32::inst::*;
use crate::isa::a32::lower::emit_vm_call;
use crate::ir::*;
use crate::ir::immediates::*;
use crate::ir::types::*;
use crate::ir::condcodes::{IntCC, FloatCC};
use crate::machinst::{Reg, MachInst, SmallInstVec, VCodeConstant, VCodeConstantData, ArgPair, InstOutput, Lower};
use crate::machinst::isle::*;
use crate::machinst::valueregs;
use regalloc2::PReg;
use alloc::vec::Vec;
use alloc::boxed::Box;

type VecArgPair = Vec<ArgPair>;
type BoxCallInfo = Box<CallInfo>;
type BoxCallIndInfo = Box<CallIndInfo>;
type BoxExternalName = Box<ExternalName>;
type VecMachLabel = Vec<MachLabel>;
type VecJumpTarget = Vec<JumpTarget>;

impl IsleContext<'_, '_, MInst, A32Backend> {
    isle_prelude_method_helpers!(A32ABICaller);

    #[inline]
    fn emit_list(&mut self, list: &SmallInstVec<MInst>) {
        for i in list {
            self.lower_ctx.emit(i.clone());
        }
    }

    fn libcall<const N: usize>(&mut self, libcall: &LibCall, arg_tys: [Type; N], args: [ValueRegs; N], ret_ty: Type) -> ValueRegs {
        let call_conv = self.lower_ctx.abi().call_conv(self.lower_ctx.sigs());
        let signature = libcall.signature(call_conv);

        debug_assert_eq!(signature.params.len(), N);
        for i in 0..N {
            debug_assert_eq!(signature.params[i].value_type, arg_tys[i]);
            debug_assert_eq!(args[i].len(), ((arg_tys[i].bits() as usize) / 32).max(1));
        }
        debug_assert_eq!(signature.returns.len(), 1);
        debug_assert_eq!(signature.returns[0].value_type, ret_ty);

        let output_reg = self.lower_ctx.alloc_tmp(ret_ty);

        emit_vm_call(
            self.lower_ctx,
            &self.backend.flags,
            &self.backend.triple,
            libcall.clone(),
            &args,
            &[output_reg],
        )
        .expect("Failed to emit LibCall");

        output_reg.map(Writable::to_reg)
    }
}

impl generated_code::Context for IsleContext<'_, '_, MInst, A32Backend> {
    isle_lower_prelude_methods!();
    isle_prelude_caller_methods!(A32MachineDeps, A32ABICaller);

    fn emit(&mut self, inst: &MInst) -> Unit {
        self.lower_ctx.emit(inst.clone());
    }

    fn load_imm32(&mut self, ty: Type, val: u64) -> Reg {
        // We take a u64 here but in `lower.isle` we make sure only 32 bit or less are actually provided.
        let val = match ty {
            I8 => (val as i8) as i32,
            I16 => (val as i16) as i32,
            I32 => val as i32,
            R32 => val as i32,
            _ => unreachable!("invalid immediate type")
        };
        
        let rd = self.temp_writable_reg(ty);
        let insts = match gen_imm_pair(val) {
            ImmPair::Lower(imm) => smallvec![MInst::LoadImm { rd, imm }],
            ImmPair::Upper(uimm) => smallvec![MInst::LoadUImm { rd, uimm }],
            ImmPair::Pair(imm, uimm) => {
                let tmp = self.temp_writable_reg(ty);
                smallvec![
                    MInst::LoadUImm { rd: tmp, uimm },
                    MInst::AluRegImm { op: AluOP::Or, rd, rs: tmp.to_reg(), imm },
                ]
            }
        };

        self.emit_list(&insts);
        rd.to_reg()
    }

    fn load_imm64(&mut self, val: u64) -> ValueRegs {
        let low = self.load_imm32(I32, val & 0xFFFFFFFF);
        let high = self.load_imm32(I32, val >> 32);
        ValueRegs::two(low, high)
    }

    fn mask_shamt(&mut self, ty: Type, shamt: Reg) -> Reg {
        fn do_mask(
            ctx: &mut IsleContext<'_, '_, MInst, A32Backend>,
            ty: Type,
            shamt: Reg,
            mask: i64,
        ) -> Reg {
            let masked = ctx.temp_writable_reg(ty);
            let inst = MInst::AluRegImm {
                op: AluOP::And,
                rd: masked,
                rs: shamt,
                imm: Imm15::new(mask).unwrap(),
            };

            ctx.emit(&inst);
            masked.to_reg()
        }

        match ty {
            I8 => do_mask(self, ty, shamt, 0x7),
            I16 => do_mask(self, ty, shamt, 0xF),
            I32 | R32 => shamt,
            _ => unreachable!("invalid shift amount type")
        }
    }

    #[inline]
    fn imm15_from_u64(&mut self, val: u64) -> Option<Imm15> {
        Imm15::new(val as i64)
    }

    #[inline]
    fn shamt32_from_u64(&mut self, val: u64) -> Option<Imm15> {
        Imm15::new((val & 0x1F) as i64)
    }

    #[inline]
    fn shamt16_from_u64(&mut self, val: u64) -> Option<Imm15> {
        Imm15::new((val & 0xF) as i64)
    }

    #[inline]
    fn shamt8_from_u64(&mut self, val: u64) -> Option<Imm15> {
        Imm15::new((val & 0x7) as i64)
    }

    #[inline]
    fn zero_reg(&mut self) -> Reg {
        zero()
    }

    #[inline]
    fn zero_reg_w(&mut self) -> Writable<Reg> {
        zero_w()
    }

    #[inline]
    fn ra_reg(&mut self) -> PReg {
        P_RA
    }

    #[inline]
    fn sp_reg(&mut self) -> PReg {
        P_SP
    }

    #[inline]
    fn fp_reg(&mut self) -> PReg {
        P_S12
    }

    #[inline]
    fn imm15(&mut self, val: i16) -> Imm15 {
        Imm15::new(val as i64).unwrap()
    }

    #[inline]
    fn value_regs_four(&mut self, r1: Reg, r2: Reg, r3: Reg, r4: Reg) -> ValueRegs {
        ValueRegs::four(r1, r2, r3, r4)
    }

    #[inline]
    fn build_amode(&mut self, base: Reg, offset: Offset32) -> AMode {
        AMode::RegOffset(base, offset.into())
    }

    #[inline]
    fn add_offset(&mut self, offset: Offset32, add: i32) -> Offset32 {
        offset.try_add_i64(add as i64).expect("offset overflow")
    }

    fn is_signed_cc(&mut self, cc: &IntCC) -> bool {
        matches!(cc,
            IntCC::SignedLessThan
            | IntCC::SignedGreaterThanOrEqual
            | IntCC::SignedGreaterThan
            | IntCC::SignedLessThanOrEqual
        )
    }

    #[inline]
    fn jump_target(&mut self, elements: &VecMachLabel, idx: u8) -> JumpTarget {
        JumpTarget::Label(elements[idx as usize])
    }

    fn gen_stack_addr(&mut self, slot: StackSlot, offset: Offset32) -> Reg {
        let result = self.temp_writable_reg(I32);

        let inst = self
            .lower_ctx
            .abi()
            .sized_stackslot_addr(slot, i64::from(offset) as u32, result);
        self.emit(&inst);

        result.to_reg()
    }

    fn floatcc_mask(&mut self, cc: &FloatCC) -> Imm15 {
        const UN: u8 = 0x1;
        const EQ: u8 = 0x2;
        const LT: u8 = 0x4;
        const GT: u8 = 0x8;

        let bits = match cc {
            FloatCC::Ordered => EQ | LT | GT,
            FloatCC::Unordered => UN,
            FloatCC::Equal => EQ,
            FloatCC::NotEqual => UN | LT | GT,
            FloatCC::OrderedNotEqual => LT | GT,
            FloatCC::UnorderedOrEqual => UN | EQ,
            FloatCC::LessThan => LT,
            FloatCC::LessThanOrEqual => EQ | LT,
            FloatCC::GreaterThan => GT,
            FloatCC::GreaterThanOrEqual => EQ | GT,
            FloatCC::UnorderedOrLessThan => UN | LT,
            FloatCC::UnorderedOrLessThanOrEqual => UN | EQ | LT,
            FloatCC::UnorderedOrGreaterThan => UN | GT,
            FloatCC::UnorderedOrGreaterThanOrEqual => UN | EQ | GT,
        };

        Imm15::new(bits as i64).unwrap()
    }

    fn load_ext_name(&mut self, name: ExternalName, offset: i64) -> Reg {
        let tmp = self.temp_writable_reg(I32);
        self.emit(&MInst::LoadExtName {
            rd: tmp,
            name: Box::new(name),
            offset,
        });
        tmp.to_reg()
    }

    fn libcall_1(&mut self, libcall: &LibCall, a_ty: Type, a: ValueRegs, ret_ty: Type) -> ValueRegs {
        self.libcall(libcall, [a_ty], [a], ret_ty)
    }

    fn libcall_2(&mut self, libcall: &LibCall, a_ty: Type, a: ValueRegs, b_ty: Type, b: ValueRegs, ret_ty: Type) -> ValueRegs {
        self.libcall(libcall, [a_ty, b_ty], [a, b], ret_ty)
    }

    fn libcall_3(&mut self, libcall: &LibCall, a_ty: Type, a: ValueRegs, b_ty: Type, b: ValueRegs, c_ty: Type, c: ValueRegs, ret_ty: Type) -> ValueRegs {
        self.libcall(libcall, [a_ty, b_ty, c_ty], [a, b, c], ret_ty)
    }

    fn lower_jump_table(&mut self, index: ValueRegs, targets: &VecMachLabel) -> Unit {
        let tmp = self.temp_writable_reg(I32);

        let targets: Vec<JumpTarget> = targets
            .into_iter()
            .copied()
            .map(JumpTarget::Label)
            .collect();

        self.emit(&MInst::JumpTable {
            index: index.regs()[0],
            tmp,
            targets,
        });
    }
}

/// The main entry point for lowering with ISLE.
pub(crate) fn lower(
    lower_ctx: &mut Lower<MInst>,
    backend: &A32Backend,
    inst: Inst,
) -> Option<InstOutput> {
    // TODO: reuse the ISLE context across lowerings so we can reuse its
    // internal heap allocations.
    let mut isle_ctx = IsleContext { lower_ctx, backend };
    generated_code::constructor_lower(&mut isle_ctx, inst)
}

/// The main entry point for branch lowering with ISLE.
pub(crate) fn lower_branch(
    lower_ctx: &mut Lower<MInst>,
    backend: &A32Backend,
    branch: Inst,
    targets: &[MachLabel],
) -> Option<()> {
    // TODO: reuse the ISLE context across lowerings so we can reuse its
    // internal heap allocations.
    let mut isle_ctx = IsleContext { lower_ctx, backend };
    generated_code::constructor_lower_branch(&mut isle_ctx, branch, &targets.to_vec())
}
