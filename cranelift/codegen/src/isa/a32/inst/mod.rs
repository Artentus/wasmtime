//! This module defines A32-specific machine instruction types.

// Some variants are not constructed, but we still want them as options in the future.
#![allow(dead_code)]
#![allow(non_camel_case_types)]

use crate::binemit::{Addend, CodeOffset, Reloc};
use crate::ir::condcodes::IntCC;
use crate::ir::types::{I8, I16, I32, I64, I128, R32, F32, F64};
pub use crate::ir::{ExternalName, MemFlags, Opcode, SourceLoc, Type, ValueLabel};
use crate::isa::CallConv;
use crate::machinst::*;
use crate::{settings, CodegenError, CodegenResult};
use crate::isa::a32::abi::A32MachineDeps;
use alloc::borrow::ToOwned;
use regalloc2::{PRegSet, VReg};
use smallvec::smallvec;
use std::string::{String, ToString};
use std::fmt::{Display, Formatter};
use std::vec::Vec;

pub mod regs;
pub use self::regs::*;
pub mod imms;
pub use self::imms::*;
pub mod args;
pub use self::args::*;
pub mod emit;
pub use self::emit::*;

pub use crate::isa::a32::lower::isle::generated_code::{
    AluOP, LoadOP, StoreOP, MInst,
};

pub(crate) type OptReg = Option<Reg>;
pub(crate) type OptImm15 = Option<Imm15>;
pub(crate) type OptImm22 = Option<Imm22>;
pub(crate) type OptUImm20 = Option<UImm20>;

/// Different forms of label references for different instruction formats.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LabelUse {
    PCRel22,
    PCRel32,
}

impl MachInstLabelUse for LabelUse {
    const ALIGN: CodeOffset = 4;

    fn max_pos_range(self) -> CodeOffset {
        match self {
            LabelUse::PCRel22 => (1 << 21) - 1,
            LabelUse::PCRel32 => (1 << 31) - 1,
        }
    }

    fn max_neg_range(self) -> CodeOffset {
        match self {
            LabelUse::PCRel22 => 1 << 21,
            LabelUse::PCRel32 => 1 << 31,
        }
    }

    fn patch_size(self) -> CodeOffset {
        match self {
            LabelUse::PCRel22 => 4,
            LabelUse::PCRel32 => 8,
        }
    }

    fn patch(self, buffer: &mut [u8], use_offset: CodeOffset, label_offset: CodeOffset) {
        assert!((use_offset % 4) == 0);
        assert!((label_offset % 4) == 0);

        let offset = (label_offset as i64) - (use_offset as i64);
        assert!(offset >= -(self.max_neg_range() as i64));
        assert!(offset <= (self.max_pos_range() as i64));

        self.patch_raw_offset(buffer, offset as i32);
    }

    fn supports_veneer(self) -> bool {
        match self {
            LabelUse::PCRel22 => true,
            LabelUse::PCRel32 => false,
        }
    }

    fn veneer_size(self) -> CodeOffset {
        match self {
            LabelUse::PCRel22 => 8,
            LabelUse::PCRel32 => unreachable!("label does not support veneer"),
        }
    }

    fn generate_veneer(self, buffer: &mut [u8], veneer_offset: CodeOffset) -> (CodeOffset, Self) {
        let inst_word = encode_addpcui(t7_w(), UImm20::ZERO);
        buffer[0..4].copy_from_slice(&inst_word.to_le_bytes());

        let inst_word = encode_jump(t7(), zero_w(), Imm15::ZERO);
        buffer[4..8].copy_from_slice(&inst_word.to_le_bytes());

        (veneer_offset, LabelUse::PCRel32)
    }

    fn from_reloc(reloc: Reloc, addend: Addend) -> Option<Self> {
        match (reloc, addend) {
            (Reloc::A32Call, _) => Some(LabelUse::PCRel32),
            _ => None,
        }
    }
}

impl LabelUse {
    fn patch_raw_offset(self, buffer: &mut [u8], offset: i32) {
        match self {
            LabelUse::PCRel22 => {
                let imm = Imm22::new(offset as i64).expect("veneer not generated");
                let imm_bin = imm.bits();

                let mut inst_word = u32::from_le_bytes([buffer[0], buffer[1], buffer[2], buffer[3]]);
                inst_word |= ((imm_bin & 0x20_0000) << 10) | ((imm_bin & 0x3FFC) << 17) | ((imm_bin & 0x1F_C000) >> 2);
                buffer[0..4].copy_from_slice(&inst_word.to_le_bytes());
            }
            LabelUse::PCRel32 => {
                let (imm, uimm) = match gen_imm_pair(offset) {
                    ImmPair::Lower(imm) => (Some(imm), None),
                    ImmPair::Upper(uimm) => (None, Some(uimm)),
                    ImmPair::Pair(imm, uimm) => (Some(imm), Some(uimm)),
                };

                if let Some(uimm) = uimm {
                    let uimm_bin = uimm.bits();

                    let mut inst_word = u32::from_le_bytes([buffer[0], buffer[1], buffer[2], buffer[3]]);
                    inst_word |= (uimm_bin & 0x8000_0000) | ((uimm_bin & 0x3000) << 17) | ((uimm_bin & 0x7FFF_C000) >> 2);
                    buffer[0..4].copy_from_slice(&inst_word.to_le_bytes());
                }
                
                if let Some(imm) = imm {
                    let imm_bin = imm.bits();

                    let mut inst_word = u32::from_le_bytes([buffer[4], buffer[5], buffer[6], buffer[7]]);
                    inst_word |= imm_bin << 17;
                    buffer[4..8].copy_from_slice(&inst_word.to_le_bytes());
                }
            }
        }
    }
}

/// A jump target. Either unresolved (basic-block index) or resolved (offset
/// from end of current instruction).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JumpTarget {
    /// An unresolved reference to a Label, as passed into
    /// `lower_branch_group()`.
    Label(MachLabel),
    /// A fixed PC offset.
    ResolvedOffset(i32),
}

impl JumpTarget {
    /// Return the target's label, if it is a label-based target.
    pub(crate) fn as_label(self) -> Option<MachLabel> {
        match self {
            JumpTarget::Label(l) => Some(l),
            _ => None,
        }
    }
    /// offset zero.
    #[inline]
    pub(crate) fn zero() -> Self {
        Self::ResolvedOffset(0)
    }
    #[inline]
    pub(crate) fn offset(off: i32) -> Self {
        Self::ResolvedOffset(off)
    }
    #[inline]
    pub(crate) fn is_zero(self) -> bool {
        match self {
            JumpTarget::Label(_) => false,
            JumpTarget::ResolvedOffset(off) => off == 0,
        }
    }
    #[inline]
    pub(crate) fn as_offset(self) -> Option<i32> {
        match self {
            JumpTarget::Label(_) => None,
            JumpTarget::ResolvedOffset(off) => Some(off),
        }
    }
}

impl Display for JumpTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            JumpTarget::Label(l) => write!(f, "{}", l.to_string()),
            JumpTarget::ResolvedOffset(off) => write!(f, "{}", off),
        }
    }
}

/// Additional information for Call instructions
#[derive(Clone, Debug)]
pub struct CallInfo {
    pub dest: ExternalName,
    pub uses: CallArgList,
    pub defs: CallRetList,
    pub opcode: Opcode,
    pub caller_callconv: CallConv,
    pub callee_callconv: CallConv,
    pub clobbers: PRegSet,
}

/// Additional information for CallInd instructions
#[derive(Clone, Debug)]
pub struct CallIndInfo {
    pub rn: Reg,
    pub uses: CallArgList,
    pub defs: CallRetList,
    pub opcode: Opcode,
    pub caller_callconv: CallConv,
    pub callee_callconv: CallConv,
    pub clobbers: PRegSet,
}

impl MInst {
    pub(crate) fn load_imm32(rd: Writable<Reg>, val: i32) -> SmallInstVec<MInst> {
        match gen_imm_pair(val) {
            ImmPair::Lower(imm) => smallvec![MInst::LoadImm { rd, imm }],
            ImmPair::Upper(uimm) => smallvec![MInst::LoadUImm { rd, uimm }],
            ImmPair::Pair(imm, uimm) => smallvec![
                MInst::LoadUImm { rd, uimm },
                MInst::AluRegImm { op: AluOP::Or, rd, rs: rd.to_reg(), imm },
            ],
        }
    }
}

impl MachInst for MInst {
    type LabelUse = LabelUse;
    type ABIMachineSpec = A32MachineDeps;

    fn get_operands<F: Fn(VReg) -> VReg>(&self, collector: &mut OperandCollector<'_, F>) {
        match self {
            MInst::Nop0 => {}
            MInst::Nop4 => {}
            MInst::Brk => {}
            MInst::Hlt => {}
            MInst::Err { .. } => {}
            MInst::Syscall => {}
            MInst::ClearKFlag => {}
            &MInst::AluRegReg { rd, rs1, rs2, .. } => {
                collector.reg_use(rs1);
                collector.reg_use(rs2);
                collector.reg_def(rd);
            }
            &MInst::AluRegImm { rd, rs, .. } => {
                collector.reg_use(rs);
                collector.reg_def(rd);
            }
            &MInst::CmpRegReg { rs1, rs2, .. } => {
                collector.reg_use(rs1);
                collector.reg_use(rs2);
            }
            &MInst::CmpBRegReg { rs1, rs2, .. } => {
                collector.reg_use(rs1);
                collector.reg_use(rs2);
            }
            &MInst::CmpRegImm { rs, .. } => {
                collector.reg_use(rs);
            }
            &MInst::CmpBRegImm { rs, .. } => {
                collector.reg_use(rs);
            }
            &MInst::BitRegImm { rs, .. } => {
                collector.reg_use(rs);
            }
            MInst::SPAdj { .. } => {}
            &MInst::Load { rd, mode, .. } => {
                if let Some(base) = mode.base() {
                    collector.reg_use(base);
                }
                collector.reg_def(rd);
            }
            &MInst::Store { rs, mode, .. } => {
                if let Some(base) = mode.base() {
                    collector.reg_use(base);
                }
                collector.reg_use(rs);
            }
            &MInst::Jump { link, base, .. } => {
                collector.reg_use(base);
                collector.reg_def(link);
            }
            &MInst::LoadUImm { rd, .. } => {
                collector.reg_def(rd);
            }
            &MInst::AddPcUImm { rd, .. } => {
                collector.reg_def(rd);
            }
            MInst::Branch { .. } => {}
            MInst::JumpRel { .. } => {}
            &MInst::CondMoveRegReg { rd, rs1, rs2, .. } => {
                collector.reg_use(rs1);
                collector.reg_use(rs2);
                collector.reg_def(rd);
            }
            &MInst::Move { rd, rs } => {
                collector.reg_use(rs);
                collector.reg_def(rd);
            }
            &MInst::MoveFromPReg { rd, .. } => {
                collector.reg_def(rd);
            }
            &MInst::CondMoveRegImm { rd, rs, .. } => {
                collector.reg_use(rs);
                collector.reg_def(rd);
            }
            &MInst::LoadImm { rd, .. } => {
                collector.reg_def(rd);
            }
            MInst::Args { args } => {
                for arg in args {
                    collector.reg_fixed_def(arg.vreg, arg.preg);
                }
            }
            &MInst::DummyUse { reg } => {
                collector.reg_use(reg);
            }
            MInst::Ret { rets } => {
                for ret in rets {
                    collector.reg_fixed_use(ret.vreg, ret.preg);
                }
            }
            &MInst::Extend { rd, rs, .. } => {
                collector.reg_use(rs);
                collector.reg_def(rd);
            }
            MInst::Call { info } => {
                for u in &info.uses {
                    collector.reg_fixed_use(u.vreg, u.preg);
                }
                for d in &info.defs {
                    collector.reg_fixed_def(d.vreg, d.preg);
                }
                collector.reg_clobbers(info.clobbers);
            }
            MInst::CallInd { info } => {
                collector.reg_use(info.rn);
                for u in &info.uses {
                    collector.reg_fixed_use(u.vreg, u.preg);
                }
                for d in &info.defs {
                    collector.reg_fixed_def(d.vreg, d.preg);
                }
                collector.reg_clobbers(info.clobbers);
            }
            &MInst::LoadExtName { rd, .. } => {
                collector.reg_def(rd);
            }
            MInst::NominalSPAdj { .. } => {}
            &MInst::LoadAddr { rd, mode } => {
                if let Some(base) = mode.base() {
                    collector.reg_use(base);
                }
                collector.reg_early_def(rd);
            }
            &MInst::JumpTable { index, tmp, .. } => {
                collector.reg_use(index);
                collector.reg_early_def(tmp);
            }
        }
    }

    fn is_move(&self) -> Option<(Writable<Reg>, Reg)> {
        if let &MInst::Move { rd, rs } = self {
            Some((rd, rs))
        } else {
            None
        }
    }

    fn is_term(&self) -> MachTerminator {
        match self {
            MInst::Jump { .. } => MachTerminator::Uncond,
            MInst::Branch { .. } => MachTerminator::Cond,
            MInst::JumpRel { .. } => MachTerminator::Uncond,
            MInst::Ret { .. } => MachTerminator::Ret,
            MInst::JumpTable { .. } => MachTerminator::Indirect,
            _ => MachTerminator::None
        }
    }

    fn is_trap(&self) -> bool {
        match self {
            MInst::Brk => true,
            MInst::Hlt => true,
            MInst::Err { .. } => true,
            _ => false,
        }
    }

    fn is_args(&self) -> bool {
        matches!(self, MInst::Args { .. })
    }

    fn is_included_in_clobbers(&self) -> bool {
        !matches!(self, MInst::Args { .. })
    }

    fn gen_move(to_reg: Writable<Reg>, from_reg: Reg, _ty: Type) -> Self {
        MInst::Move { rd: to_reg, rs: from_reg }
    }

    fn gen_dummy_use(reg: Reg) -> Self {
        MInst::DummyUse { reg }
    }

    fn rc_for_type(ty: Type) -> CodegenResult<(&'static [RegClass], &'static [Type])> {
        match ty {
            I8 => Ok((&[RegClass::Int], &[I8])),
            I16 => Ok((&[RegClass::Int], &[I16])),
            I32 => Ok((&[RegClass::Int], &[I32])),
            I64 => Ok((&[RegClass::Int, RegClass::Int], &[I32, I32])),
            I128 => Ok((&[RegClass::Int, RegClass::Int, RegClass::Int, RegClass::Int], &[I32, I32, I32, I32])),
            R32 => Ok((&[RegClass::Int], &[R32])),
            F32 => Ok((&[RegClass::Int], &[I32])),
            F64 => Ok((&[RegClass::Int, RegClass::Int], &[I32, I32])),
            _ => Err(CodegenError::Unsupported(format!(
                "Unsupported SSA-value type: {}",
                ty
            ))),
        }
    }

    fn canonical_type_for_rc(rc: RegClass) -> Type {
        match rc {
            regalloc2::RegClass::Int => I32,
            regalloc2::RegClass::Float => unreachable!("A32 does not have floating point registers"),
        }
    }

    fn gen_jump(target: MachLabel) -> Self {
        MInst::JumpRel {
            target: JumpTarget::Label(target),
        }
    }

    fn gen_nop(preferred_size: usize) -> Self {
        if preferred_size == 0 {
            MInst::Nop0
        } else {
            // We can't give a NOP < 4 bytes.
            assert!(preferred_size >= 4);
            MInst::Nop4
        }
    }

    fn worst_case_size() -> CodeOffset {
        16 // 4 words
    }

    fn ref_type_regclass(_flags: &settings::Flags) -> RegClass {
        RegClass::Int
    }

    fn is_safepoint(&self) -> bool {
        matches!(self,
            | MInst::Err { .. }
            | MInst::Call { .. }
            | MInst::CallInd { .. }
        )
    }
}

//=============================================================================
// Pretty-printing of instructions.
pub(crate) fn reg_name(reg: Reg) -> String {
    match reg.to_real_reg() {
        Some(real) => match real.class() {
            RegClass::Int => match real.hw_enc() {
                0 => "zero".into(),
                1 => "ra".into(),
                2 => "sp".into(),
                3..=10 => format!("a{}", real.hw_enc() - 3),
                11..=18 => format!("t{}", real.hw_enc() - 11),
                19..=31 => format!("s{}", real.hw_enc() - 19),
                _ => unreachable!(),
            },
            RegClass::Float => unreachable!("A32 does not have floating point registers"),
        },
        None => {
            format!("{:?}", reg)
        }
    }
}

fn format_reg(reg: Reg, allocs: &mut AllocationConsumer<'_>) -> String {
    let reg = allocs.next(reg);
    reg_name(reg)
}

fn format_target(target: JumpTarget) -> String {
    match target {
        JumpTarget::Label(label) => format!("{:?}", label),
        JumpTarget::ResolvedOffset(offset) => format!("{:+}", offset),
    }
}

fn alu_op_name(op: AluOP) -> &'static str {
    match op {
        AluOP::Add => "add",
        AluOP::AddC => "addc",
        AluOP::Sub => "sub",
        AluOP::SubB => "subb",
        AluOP::And => "and",
        AluOP::Or => "or",
        AluOP::Xor => "xor",
        AluOP::Shl => "shl",
        AluOP::Lsr => "lsr",
        AluOP::Asr => "asr",
        AluOP::Mul => "mul",
        AluOP::MulHuu => "mulhuu",
        AluOP::MulHss => "mulhss",
        AluOP::MulHus => "mulhus",
    }
}

fn load_op_name(op: LoadOP) -> &'static str {
    match op {
        LoadOP::Ld32 => "ld",
        LoadOP::Ld8 => "ld8",
        LoadOP::Ld8S => "ld8s",
        LoadOP::Ld16 => "ld16",
        LoadOP::Ld16S => "ld16s",
        LoadOP::In => "in",
    }
}

fn store_op_name(op: StoreOP) -> &'static str {
    match op {
        StoreOP::St32 => "st",
        StoreOP::St8 => "st8",
        StoreOP::St16 => "st16",
        StoreOP::Out => "out",
    }
}

fn cc_name(cc: IntCC) -> &'static str {
    match cc {
        IntCC::Equal => "eq",
        IntCC::NotEqual => "neq",
        IntCC::SignedLessThan => "s.l",
        IntCC::SignedGreaterThanOrEqual => "s.ge",
        IntCC::SignedGreaterThan => "s.g",
        IntCC::SignedLessThanOrEqual => "s.le",
        IntCC::UnsignedLessThan => "u.l",
        IntCC::UnsignedGreaterThanOrEqual => "u.ge",
        IntCC::UnsignedGreaterThan => "u.g",
        IntCC::UnsignedLessThanOrEqual => "u.le",
    }
}

impl MInst {
    fn print_with_state(
        &self,
        state: &mut EmitState,
        allocs: &mut AllocationConsumer,
    ) -> String {
        match self {
            MInst::Nop0 => "nop0".to_owned(),
            MInst::Nop4 => "nop".to_owned(),
            MInst::Brk => "brk".to_owned(),
            MInst::Hlt => "hlt".to_owned(),
            MInst::Err { .. } => "err".to_owned(),
            MInst::Syscall => "sys".to_owned(),
            MInst::ClearKFlag => "clrk".to_owned(),
            &MInst::AluRegReg { op, rd, rs1, rs2 } => {
                let rs1 = format_reg(rs1, allocs);
                let rs2 = format_reg(rs2, allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("{} {}, {}, {}", alu_op_name(op), rd, rs1, rs2)
            }
            &MInst::AluRegImm { op, rd, rs, imm } => {
                let rs = format_reg(rs, allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("{} {}, {}, {}", alu_op_name(op), rd, rs, imm)
            }
            &MInst::CmpRegReg { rs1, rs2 } => {
                let rs1 = format_reg(rs1, allocs);
                let rs2 = format_reg(rs2, allocs);
                format!("cmp {}, {}", rs1, rs2)
            }
            &MInst::CmpBRegReg { rs1, rs2 } => {
                let rs1 = format_reg(rs1, allocs);
                let rs2 = format_reg(rs2, allocs);
                format!("cmpb {}, {}", rs1, rs2)
            }
            &MInst::CmpRegImm { rs, imm } => {
                let rs = format_reg(rs, allocs);
                format!("cmp {}, {}", rs, imm)
            }
            &MInst::CmpBRegImm { rs, imm } => {
                let rs = format_reg(rs, allocs);
                format!("cmpb {}, {}", rs, imm)
            }
            &MInst::SPAdj { amount } => {
                format!("sp_adj {:+}", amount)
            }
            &MInst::BitRegImm { rs, imm } => {
                let rs = format_reg(rs, allocs);
                format!("bit {}, {}", rs, imm)
            }
            &MInst::Load { op, rd, mode } => {
                let base = mode.pbase_name(allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("{} {}, [{}, {}]", load_op_name(op), rd, base, mode.offset(state))
            }
            &MInst::Store { op, rs, mode } => {
                let base = mode.pbase_name(allocs);
                let rs = format_reg(rs, allocs);
                format!("{} [{}, {}], {}", store_op_name(op), base, mode.offset(state), rs)
            }
            &MInst::Jump { link, base, offset } => {
                let link = format_reg(link.to_reg(), allocs);
                let base = format_reg(base, allocs);
                format!("jl {}, {}, {}", link, base, offset)
            }
            &MInst::LoadUImm { rd, uimm } => {
                let rd = format_reg(rd.to_reg(), allocs);
                format!("ldui {}, {}", rd, uimm)
            }
            &MInst::AddPcUImm { rd, uimm } => {
                let rd = format_reg(rd.to_reg(), allocs);
                format!("addpcui {}, {}", rd, uimm)
            }
            &MInst::Branch { cc, taken, not_taken } => {
                let taken = format_target(taken);
                let not_taken = format_target(not_taken);
                format!("br.{} {}, {}", cc_name(cc), taken, not_taken)
            }
            &MInst::JumpRel { target } => {
                let target = format_target(target);
                format!("jr {}", target)
            }
            &MInst::CondMoveRegReg { cc, rd, rs1, rs2 } => {
                let rs1 = format_reg(rs1, allocs);
                let rs2 = format_reg(rs2, allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("mv.{} {}, {}, {}", cc_name(cc), rd, rs1, rs2)
            }
            &MInst::Move { rd, rs } => {
                let rs = format_reg(rs, allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("mov {}, {}", rd, rs)
            }
            &MInst::MoveFromPReg { rd, rs } => {
                let rs = format_reg(rs.into(), allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("mov {}, {}", rd, rs)
            }
            &MInst::CondMoveRegImm { cc, rd, rs, imm } => {
                let rs = format_reg(rs, allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("mv.{} {}, {}, {}", cc_name(cc), rd, rs, imm)
            }
            &MInst::LoadImm { rd, imm } => {
                let rd = format_reg(rd.to_reg(), allocs);
                format!("ldi {}, {}", rd, imm)
            }
            MInst::Args { args } => {
                let mut s = "args".to_string();
                let mut empty_allocs = AllocationConsumer::default();
                for arg in args {
                    use std::fmt::Write;
                    let preg = format_reg(arg.preg, &mut empty_allocs);
                    let def = format_reg(arg.vreg.to_reg(), allocs);
                    write!(&mut s, " {}={}", def, preg).unwrap();
                }
                s
            }
            &MInst::DummyUse { reg } => {
                let reg = format_reg(reg, allocs);
                format!("dummy_use {}", reg)
            }
            MInst::Ret { rets } => {
                let mut s = "ret".to_string();
                let mut empty_allocs = AllocationConsumer::default();
                for ret in rets {
                    use std::fmt::Write;
                    let preg = format_reg(ret.preg, &mut empty_allocs);
                    let vreg = format_reg(ret.vreg, allocs);
                    write!(&mut s, " {}={}", vreg, preg).unwrap();
                }
                s
            }
            &MInst::Extend { rd, rs, signed, from_bits, .. } => {
                let rs = format_reg(rs, allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!(
                    "{}ext{} {}, {}",
                    if signed { "s" } else { "z" },
                    from_bits,
                    rd,
                    rs
                )
            }
            MInst::Call { info } => format!("call {}", info.dest.display(None)),
            MInst::CallInd { info } => {
                let rd = format_reg(info.rn, allocs);
                format!("call_ind {}", rd)
            }
            &MInst::LoadExtName {
                rd,
                ref name,
                offset,
            } => {
                let rd = format_reg(rd.to_reg(), allocs);
                format!("load_sym {}, {}{:+}", rd, name.display(None), offset)
            }
            &MInst::NominalSPAdj { amount } => {
                format!("nom_sp_adj {:+}", amount)
            }
            &MInst::LoadAddr { rd, mode } => {
                let base = mode.pbase_name(allocs);
                let rd = format_reg(rd.to_reg(), allocs);
                format!("load_addr {}, {}{:+}", rd, base, mode.offset(state))
            }
            &MInst::JumpTable { index, tmp, ref targets } => {
                fn format_labels(labels: &[MachLabel]) -> String {
                    let mut s = String::new();
                    s.push('[');

                    for (i, l) in labels.iter().enumerate() {
                        if i > 0 {
                            s.push_str(", ");
                        }

                        use std::fmt::Write;
                        write!(s, "{:?}", l).unwrap();
                    }

                    s.push(']');
                    s
                }

                let targets: Vec<_> = targets.iter().map(|x| x.as_label().unwrap()).collect();
                format!(
                    "jump_table tmp={} {}, {}",
                    format_reg(tmp.to_reg(), allocs),
                    format_reg(index, allocs),
                    format_labels(&targets[..]),
                )
            }
        }
    }
}
