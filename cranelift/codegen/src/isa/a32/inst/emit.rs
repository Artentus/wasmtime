//! A32 ISA: binary code emission.

use crate::binemit::StackMap;
use crate::isa::a32::inst::*;
use crate::ir::RelSourceLoc;
use crate::ir::condcodes::CondCode;

/// State carried between emissions of a sequence of instructions.
#[derive(Default, Clone, Debug)]
pub struct EmitState {
    pub(crate) nominal_sp_offset: i32,
    pub(crate) nominal_sp_to_fp: i32,
    /// Safepoint stack map for upcoming instruction, as provided to `pre_safepoint()`.
    stack_map: Option<StackMap>,
    /// Current source-code location corresponding to instruction to be emitted.
    cur_srcloc: RelSourceLoc,
}

impl EmitState {
    fn take_stack_map(&mut self) -> Option<StackMap> {
        self.stack_map.take()
    }

    fn clear_post_insn(&mut self) {
        self.stack_map = None;
    }

    fn cur_srcloc(&self) -> RelSourceLoc {
        self.cur_srcloc
    }
}

impl MachInstEmitState<MInst> for EmitState {
    fn new(abi: &Callee<crate::isa::a32::abi::A32MachineDeps>) -> Self {
        EmitState {
            nominal_sp_offset: 0,
            nominal_sp_to_fp: abi.frame_size() as i32,
            stack_map: None,
            cur_srcloc: RelSourceLoc::default(),
        }
    }

    fn pre_safepoint(&mut self, stack_map: StackMap) {
        self.stack_map = Some(stack_map);
    }

    fn pre_sourceloc(&mut self, srcloc: RelSourceLoc) {
        self.cur_srcloc = srcloc;
    }
}

pub struct EmitInfo {
    shared_flag: crate::settings::Flags,
    isa_flags: crate::isa::a32::settings::Flags,
}

impl EmitInfo {
    pub(crate) fn new(
        shared_flag: crate::settings::Flags,
        isa_flags: crate::isa::a32::settings::Flags,
    ) -> Self {
        Self {
            shared_flag,
            isa_flags,
        }
    }
}

fn get_reg_bin(reg: Reg) -> u32 {
    reg.to_real_reg().unwrap().hw_enc() as u32
}

fn get_alu_op_bin(op: AluOP) -> u32 {
    match op {
        AluOP::Add => 0x0,
        AluOP::AddC => 0x1,
        AluOP::Sub => 0x2,
        AluOP::SubB => 0x3,
        AluOP::And => 0x4,
        AluOP::Or => 0x5,
        AluOP::Xor => 0x6,
        AluOP::Shl => 0x7,
        AluOP::Lsr => 0x8,
        AluOP::Asr => 0x9,
        AluOP::Mul => 0xA,
        AluOP::MulHuu => 0xB,
        AluOP::MulHss => 0xC,
        AluOP::MulHus => 0xD,
    }
}

fn get_load_op_bin(op: LoadOP) -> u32 {
    match op {
        LoadOP::Ld32 => 0b0000,
        LoadOP::Ld8 => 0b0001,
        LoadOP::Ld8S => 0b0101,
        LoadOP::Ld16 => 0b0010,
        LoadOP::Ld16S => 0b0110,
        LoadOP::In => 0b0011,
    }
}

fn get_store_op_bin(op: StoreOP) -> u32 {
    match op {
        StoreOP::St32 => 0b1000,
        StoreOP::St8 => 0b1001,
        StoreOP::St16 => 0b1010,
        StoreOP::Out => 0b1011,
    }
}

fn get_cc_bin(cc: IntCC) -> u32 {
    // ---- A32 condition codes ----
    // Carry                = 0x1
    // Zero                 = 0x2
    // Sign                 = 0x3
    // Overflow             = 0x4
    // NotCarry             = 0x5
    // NotZero              = 0x6
    // NotSign              = 0x7
    // NotOverflow          = 0x8
    // UnsignedLessOrEqual  = 0x9
    // UnsignedGreater      = 0xA
    // SignedLess           = 0xB
    // SignedGreaterOrEqual = 0xC
    // SignedLessOrEqual    = 0xD
    // SignedGreater        = 0xE
    // Always               = 0xF

    match cc {
        IntCC::Equal => 0x2, // same as Zero
        IntCC::NotEqual => 0x6, // same as NotZero
        IntCC::SignedLessThan => 0xB,
        IntCC::SignedGreaterThanOrEqual => 0xC,
        IntCC::SignedGreaterThan => 0xE,
        IntCC::SignedLessThanOrEqual => 0xD,
        IntCC::UnsignedLessThan => 0x5, // same as NotCarry
        IntCC::UnsignedGreaterThanOrEqual => 0x1, // same as Carry
        IntCC::UnsignedGreaterThan => 0xA,
        IntCC::UnsignedLessThanOrEqual => 0x9,
    }
}

fn emit_load_imm32_into_t7(
    code: &mut MachBuffer<MInst>,
    emit_info: &EmitInfo,
    state: &mut EmitState,
    imm: Option<Imm15>,
    uimm: UImm20,
) {
    let ldui = MInst::LoadUImm { rd: t7_w(), uimm };
    ldui.emit(&[], code, emit_info, state);

    if let Some(imm) = imm {
        let or = MInst::AluRegImm { op: AluOP::Or, rd: t7_w(), rs: t7(), imm };
        or.emit(&[], code, emit_info, state);
    }
}

fn emit_offset_base_into_t7(
    code: &mut MachBuffer<MInst>,
    emit_info: &EmitInfo,
    state: &mut EmitState,
    base: Reg,
    uimm: UImm20,
) {
    let ldui = MInst::LoadUImm { rd: t7_w(), uimm };
    ldui.emit(&[], code, emit_info, state);

    let add = MInst::AluRegReg { op: AluOP::Add, rd: t7_w(), rs1: base, rs2: t7() };
    add.emit(&[], code, emit_info, state);
}

pub(crate) fn encode_addpcui(rd: Writable<Reg>, uimm: UImm20) -> u32 {
    let rd_bin = get_reg_bin(rd.to_reg());
    let ui_bin = uimm.bits();

    (ui_bin & 0x8000_0000)
        | ((ui_bin & 0x3000) << 17)
        | ((ui_bin & 0x7FFF_C000) >> 2)
        | (rd_bin << 7)
        | (0x9 << 3)
        | 0b100
}

pub(crate) fn encode_jump(base: Reg, link: Writable<Reg>, offset: Imm15) -> u32 {
    let link_bin = get_reg_bin(link.to_reg());
    let base_bin = get_reg_bin(base);

    (offset.bits() << 17)
        | (base_bin << 12)
        | (link_bin << 7)
        | (0x0 << 3)
        | 0b100
}

impl MachInstEmit for MInst {
    type State = EmitState;
    type Info = EmitInfo;

    fn emit(
        &self,
        allocs: &[regalloc2::Allocation],
        code: &mut MachBuffer<Self>,
        emit_info: &Self::Info,
        state: &mut Self::State,
    ) {
        let mut allocs = AllocationConsumer::new(allocs);

        // N.B.: we *must* not exceed the "worst-case size" used to compute
        // where to insert islands, except when islands are explicitly triggered
        // (with an `EmitIsland`). We check this in debug builds. This is `mut`
        // to allow disabling the check for `JTSequence`, which is always
        // emitted following an `EmitIsland`.
        let mut start_offset = code.cur_offset();

        match self {
            MInst::Nop0 => { /* do nothing */ },
            MInst::Nop4 => code.put4((0x0 << 3) | 0b000),
            MInst::Brk => code.put4((0x1 << 3) | 0b000),
            MInst::Hlt => code.put4((0x2 << 3) | 0b000),
            &MInst::Err { trap_code } => {
                code.add_trap(trap_code);
                if let Some(s) = state.take_stack_map() {
                    code.add_stack_map(StackMapExtent::UpcomingBytes(4), s);
                }

                code.put4((0x3 << 3) | 0b000);
            }
            MInst::Syscall => code.put4((0x8 << 3) | 0b000),
            MInst::ClearKFlag => code.put4((0x9 << 3) | 0b000),
            &MInst::AluRegReg { op, rd, rs1, rs2 } => {
                let rs1 = allocs.next(rs1);
                let rs2 = allocs.next(rs2);
                let rd = allocs.next_writable(rd);
                
                let op_bin = get_alu_op_bin(op);
                let rd_bin = get_reg_bin(rd.to_reg());
                let rs1_bin = get_reg_bin(rs1);
                let rs2_bin = get_reg_bin(rs2);

                code.put4((rs2_bin << 17) | (rs1_bin << 12) | (rd_bin << 7) | (op_bin << 3) | 0b001);
            }
            &MInst::AluRegImm { op, rd, rs, imm } => {
                let rs = allocs.next(rs);
                let rd = allocs.next_writable(rd);

                let op_bin = get_alu_op_bin(op);
                let rd_bin = get_reg_bin(rd.to_reg());
                let rs_bin = get_reg_bin(rs);

                code.put4((imm.bits() << 17) | (rs_bin << 12) | (rd_bin << 7) | (op_bin << 3) | 0b010);
            }
            &MInst::CmpRegReg { rs1, rs2 } => {
                let rs1 = allocs.next(rs1);
                let rs2 = allocs.next(rs2);
                let rd = zero_w();
                
                let inst = MInst::AluRegReg { op: AluOP::Sub, rd, rs1, rs2 };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::CmpBRegReg { rs1, rs2 } => {
                let rs1 = allocs.next(rs1);
                let rs2 = allocs.next(rs2);
                let rd = zero_w();
                
                let inst = MInst::AluRegReg { op: AluOP::SubB, rd, rs1, rs2 };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::CmpRegImm { rs, imm } => {
                let rs = allocs.next(rs);
                let rd = zero_w();

                let inst = MInst::AluRegImm { op: AluOP::Sub, rd, rs, imm };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::CmpBRegImm { rs, imm } => {
                let rs = allocs.next(rs);
                let rd = zero_w();

                let inst = MInst::AluRegImm { op: AluOP::SubB, rd, rs, imm };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::BitRegImm { rs, imm } => {
                let rs = allocs.next(rs);
                let rd = zero_w();

                let inst = MInst::AluRegImm { op: AluOP::And, rd, rs, imm };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::SPAdj { amount } => {
                match gen_imm_pair(amount) {
                    ImmPair::Lower(imm) => {
                        let inst = MInst::AluRegImm { op: AluOP::Add, rd: sp_w(), rs: sp(), imm };
                        inst.emit(&[], code, emit_info, state);
                    }
                    ImmPair::Upper(uimm) => {
                        emit_load_imm32_into_t7(code, emit_info, state, None, uimm);
                        let inst = MInst::AluRegReg { op: AluOP::Add, rd: sp_w(), rs1: sp(), rs2: t7() };
                        inst.emit(&[], code, emit_info, state);
                    }
                    ImmPair::Pair(imm, uimm) => {
                        emit_load_imm32_into_t7(code, emit_info, state, Some(imm), uimm);
                        let inst = MInst::AluRegReg { op: AluOP::Add, rd: sp_w(), rs1: sp(), rs2: t7() };
                        inst.emit(&[], code, emit_info, state);
                    }
                }
            }
            &MInst::Load { op, rd, mode } => {
                let base = mode.pbase(&mut allocs);
                let rd = allocs.next_writable(rd);

                let op_bin = get_load_op_bin(op);
                let rd_bin = get_reg_bin(rd.to_reg());

                match gen_imm_pair(mode.offset(state)) {
                    ImmPair::Lower(imm) => {
                        let base_bin = get_reg_bin(base);
                        code.put4((imm.bits() << 17) | (base_bin << 12) | (rd_bin << 7) | (op_bin << 3) | 0b011);
                    },
                    ImmPair::Upper(uimm) => {
                        emit_offset_base_into_t7(code, emit_info, state, base, uimm);
                        let base_bin = get_reg_bin(t7());
                        code.put4((0 << 17) | (base_bin << 12) | (rd_bin << 7) | (op_bin << 3) | 0b011);
                    }
                    ImmPair::Pair(imm, uimm) => {
                        emit_offset_base_into_t7(code, emit_info, state, base, uimm);
                        let base_bin = get_reg_bin(t7());
                        code.put4((imm.bits() << 17) | (base_bin << 12) | (rd_bin << 7) | (op_bin << 3) | 0b011);
                    }
                }
            }
            &MInst::Store { op, rs, mode } => {
                let base = mode.pbase(&mut allocs);
                let rs = allocs.next(rs);

                let op_bin = get_store_op_bin(op);
                let rs_bin = get_reg_bin(rs);
                
                match gen_imm_pair(mode.offset(state)) {
                    ImmPair::Lower(imm) => {
                        let base_bin = get_reg_bin(base);
                        code.put4((imm.bits() << 17) | (base_bin << 12) | (rs_bin << 7) | (op_bin << 3) | 0b011);
                    }
                    ImmPair::Upper(uimm) => {
                        emit_offset_base_into_t7(code, emit_info, state, base, uimm);
                        let base_bin = get_reg_bin(t7());
                        code.put4((0 << 17) | (base_bin << 12) | (rs_bin << 7) | (op_bin << 3) | 0b011);
                    }
                    ImmPair::Pair(imm, uimm) => {
                        emit_offset_base_into_t7(code, emit_info, state, base, uimm);
                        let base_bin = get_reg_bin(t7());
                        code.put4((imm.bits() << 17) | (base_bin << 12) | (rs_bin << 7) | (op_bin << 3) | 0b011);
                    }
                }
            }
            &MInst::Jump { link, base, offset } => {
                let base = allocs.next(base);
                let link = allocs.next_writable(link);
                code.put4(encode_jump(base, link, offset));
            }
            &MInst::LoadUImm { rd, uimm } => {
                let rd = allocs.next_writable(rd);

                let rd_bin = get_reg_bin(rd.to_reg());
                let ui_bin = uimm.bits();

                code.put4((ui_bin & 0x8000_0000)
                    | ((ui_bin & 0x3000) << 17)
                    | ((ui_bin & 0x7FFF_C000) >> 2)
                    | (rd_bin << 7)
                    | (0x8 << 3)
                    | 0b100);
            }
            &MInst::AddPcUImm { rd, uimm } => {
                let rd = allocs.next_writable(rd);
                code.put4(encode_addpcui(rd, uimm));
            }
            &MInst::Branch { cc, taken, not_taken } => {
                let cc_bin = get_cc_bin(cc);
                
                match taken {
                    JumpTarget::Label(label) => {
                        let inv_cc = cc.inverse();
                        let inv_cc_bin = get_cc_bin(inv_cc);

                        code.use_label_at_offset(start_offset, label, LabelUse::PCRel22);

                        let inv_inst_code = (inv_cc_bin << 3) | 0b101;
                        code.add_cond_branch(
                            start_offset,
                            start_offset + 4,
                            label,
                            &inv_inst_code.to_le_bytes(),
                        );

                        code.put4((cc_bin << 3) | 0b101);
                    }
                    JumpTarget::ResolvedOffset(offset) => {
                        let offset = Imm22::new(offset as i64).expect("target out of range for branch");
                        let offset = offset.bits();

                        if offset > 0 {
                            code.put4(((offset & 0x20_0000) << 10)
                                | ((offset & 0x3FFC) << 17)
                                | ((offset & 0x1F_C000) >> 2)
                                | (cc_bin << 3)
                                | 0b101);
                        }
                    }
                }

                let inst = MInst::JumpRel { target: not_taken };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::JumpRel { target } => {
                match target {
                    JumpTarget::Label(label) => {
                        code.use_label_at_offset(start_offset, label, LabelUse::PCRel22);
                        code.add_uncond_branch(start_offset, start_offset + 4, label);
                        code.put4((0xF << 3) | 0b101);
                    }
                    JumpTarget::ResolvedOffset(offset) => {
                        let offset = Imm22::new(offset as i64).expect("target out of range for jump");
                        let offset = offset.bits();

                        if offset > 0 {
                            code.put4(((offset & 0x20_0000) << 10)
                                | ((offset & 0x3FFC) << 17)
                                | ((offset & 0x1F_C000) >> 2)
                                | (0xF << 3)
                                | 0b101);
                        }
                    }
                }
            }
            &MInst::CondMoveRegReg { cc, rd, rs1, rs2 } => {
                let rs1 = allocs.next(rs1);
                let rs2 = allocs.next(rs2);
                let rd = allocs.next_writable(rd);
                
                let cc_bin = get_cc_bin(cc);
                let rd_bin = get_reg_bin(rd.to_reg());
                let rs1_bin = get_reg_bin(rs1);
                let rs2_bin = get_reg_bin(rs2);

                code.put4((rs2_bin << 17) | (rs1_bin << 12) | (rd_bin << 7) | (cc_bin << 3) | 0b110);
            }
            &MInst::Move { rd, rs } => {
                let rs = allocs.next(rs);
                let rd = allocs.next_writable(rd);
                
                let rd_bin = get_reg_bin(rd.to_reg());
                let rs_bin = get_reg_bin(rs);

                code.put4((rs_bin << 17) | (rd_bin << 7) | (0xF << 3) | 0b110);
            }
            &MInst::MoveFromPReg { rd, rs } => {
                let rs = allocs.next(Reg::from(rs));
                let rd = allocs.next_writable(rd);
                
                let rd_bin = get_reg_bin(rd.to_reg());
                let rs_bin = get_reg_bin(rs);

                code.put4((rs_bin << 17) | (rd_bin << 7) | (0xF << 3) | 0b110);
            }
            &MInst::CondMoveRegImm { cc, rd, rs, imm } => {
                let rs = allocs.next(rs);
                let rd = allocs.next_writable(rd);
                
                let cc_bin = get_cc_bin(cc);
                let rd_bin = get_reg_bin(rd.to_reg());
                let rs_bin = get_reg_bin(rs);

                code.put4((imm.bits() << 17) | (rs_bin << 12) | (rd_bin << 7) | (cc_bin << 3) | 0b111);
            }
            &MInst::LoadImm { rd, imm } => {
                let rd = allocs.next_writable(rd);
                let rd_bin = get_reg_bin(rd.to_reg());
                code.put4((imm.bits() << 17) | (rd_bin << 7) | (0xF << 3) | 0b111);
            }
            MInst::Args { .. } => {
                // This is a pseudoinstruction that serves
                // only to constrain registers at a certain point.
            }
            &MInst::DummyUse { reg } => { allocs.next(reg); }
            MInst::Ret { .. } => {
                let inst = MInst::Jump { link: zero_w(), base: ra(), offset: Imm15::ZERO };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::Extend {
                rd,
                rs,
                signed,
                from_bits,
                to_bits,
            } => {
                assert!(to_bits <= 32);
                assert!(from_bits < to_bits);
                
                let rs = allocs.next(rs);
                let rd = allocs.next_writable(rd);

                if (from_bits < 15) && !signed {
                    // special case where only one instruction is required
                    let mask = Imm15::new((1 << from_bits) - 1).unwrap();
                    let inst = MInst::AluRegImm { op: AluOP::And, rd, rs, imm: mask };

                    inst.emit(&[], code, emit_info, state);
                } else {
                    let shift = Imm15::new((32 - from_bits) as i64).unwrap();
                    let right_op = if signed { AluOP::Asr } else { AluOP::Lsr };
                    let left = MInst::AluRegImm { op: AluOP::Shl, rd, rs, imm: shift };
                    let right = MInst::AluRegImm { op: right_op, rd, rs: rd.to_reg(), imm: shift };

                    left.emit(&[], code, emit_info, state);
                    right.emit(&[], code, emit_info, state);
                }
            }
            MInst::Call { info } => {
                if let Some(s) = state.take_stack_map() {
                    code.add_stack_map(StackMapExtent::UpcomingBytes(8), s);
                }

                if info.opcode.is_call() {
                    code.add_call_site(info.opcode);
                }

                code.add_reloc(Reloc::A32Rel, &info.dest, 0);
                
                let addpcui = MInst::AddPcUImm { rd: t7_w(), uimm: UImm20::ZERO };
                let jl = MInst::Jump { link: ra_w(), base: t7(), offset: Imm15::ZERO };
                addpcui.emit(&[], code, emit_info, state);
                jl.emit(&[], code, emit_info, state);
            }
            MInst::CallInd { info } => {
                if let Some(s) = state.take_stack_map() {
                    code.add_stack_map(StackMapExtent::UpcomingBytes(4), s);
                }
            
                if info.opcode.is_call() {
                    code.add_call_site(info.opcode);
                }

                let base = allocs.next(info.rn);
                let inst = MInst::Jump {
                    link: ra_w(),
                    base,
                    offset: Imm15::ZERO,
                };
                inst.emit(&[], code, emit_info, state);
            }
            &MInst::LoadExtName {
                rd,
                ref name,
                offset,
            } => {
                let rd = allocs.next_writable(rd);

                code.add_reloc(Reloc::A32Abs, name, offset);
                
                let ldui = MInst::LoadUImm { rd: t7_w(), uimm: UImm20::ZERO };
                let or = MInst::AluRegImm { op: AluOP::Or, rd, rs: t7(), imm: Imm15::ZERO };
                ldui.emit(&[], code, emit_info, state);
                or.emit(&[], code, emit_info, state);
            }
            &MInst::NominalSPAdj { amount } => {
                state.nominal_sp_offset += amount;
                log::trace!(
                    "nominal sp offset adjusted by {} to {}",
                    amount,
                    state.nominal_sp_offset,
                );
            }
            &MInst::LoadAddr { rd, mode } => {
                let base = mode.pbase(&mut allocs);
                let rd = allocs.next_writable(rd);

                match gen_imm_pair(mode.offset(state)) {
                    ImmPair::Lower(imm) => {
                        let inst = MInst::AluRegImm { op: AluOP::Add, rd, rs: base, imm };
                        inst.emit(&[], code, emit_info, state);
                    },
                    ImmPair::Upper(uimm) => {
                        emit_load_imm32_into_t7(code, emit_info, state, None, uimm);
                        let inst = MInst::AluRegReg { op: AluOP::Add, rd, rs1: base, rs2: t7() };
                        inst.emit(&[], code, emit_info, state);
                    }
                    ImmPair::Pair(imm, uimm) => {
                        emit_load_imm32_into_t7(code, emit_info, state, Some(imm), uimm);
                        let inst = MInst::AluRegReg { op: AluOP::Add, rd, rs1: base, rs2: t7() };
                        inst.emit(&[], code, emit_info, state);
                    }
                }
            }
            &MInst::JumpTable { index, tmp, ref targets } => {
                let index = allocs.next(index);
                let tmp1 = allocs.next_writable(tmp);
                let tmp2 = t7_w();

                // The default target is passed in as the 0th element of `targets`
                let default_target = targets[0];
                let targets = &targets[1..];

                // We emit a bounds check on the index, if the index is larger than the number of
                // jump table entries, we jump to the default block.  Otherwise we compute a jump
                // offset by multiplying the index by 8 (the size of each entry) and then jump to
                // that offset. Each jump table entry is a regular auipc+jalr which we emit sequentially.
                //
                // Build the following sequence:
                // bounds_check:
                //     ldi     tmp2, n_labels
                //     cmp     index, tmp2
                //     br.u.l  compute_target
                // jump_to_default_block:
                //     jr      default_block
                // compute_target:
                //     addpcui tmp1, 0
                //     shl     tmp2, index, 2
                //     add     tmp1, tmp1, tmp2
                //     jl      zero, tmp1, 12
                // jump_table:
                //     ; This repeats for each entry in the jumptable
                //     jr     block_target

                // Load size of the table
                assert!(targets.len() <= (i32::MAX as usize));
                let insts = MInst::load_imm32(tmp2, targets.len() as i32);
                for inst in insts {
                    inst.emit(&[], code, emit_info, state);
                }

                // Bounds check
                let inst = MInst::CmpRegReg { rs1: index, rs2: tmp2.to_reg() };
                inst.emit(&[], code, emit_info, state);

                let inst = MInst::Branch {
                    cc: IntCC::UnsignedLessThan,
                    taken: JumpTarget::ResolvedOffset(4),
                    not_taken: JumpTarget::ResolvedOffset(0),
                };
                inst.emit(&[], code, emit_info, state);

                // Jump to default block
                let inst = MInst::JumpRel {
                    target: JumpTarget::Label(default_target.as_label().unwrap()),
                };
                inst.emit(&[], code, emit_info, state);

                // Compute the jump table offset.
                // We need to emit a PC relative offset,

                // Get the current PC
                let inst = MInst::AddPcUImm { rd: tmp1, uimm: UImm20::ZERO };
                inst.emit(&[], code, emit_info, state);

                // Multiply the index by 4, since that is
                // the size in bytes of each jump table entry
                let inst = MInst::AluRegImm {
                    op: AluOP::Shl,
                    rd: tmp2,
                    rs: index,
                    imm: Imm15::new(2).unwrap(),
                };
                inst.emit(&[], code, emit_info, state);
                
                // Calculate the base of the jump, PC + the offset from above
                let inst = MInst::AluRegReg {
                    op: AluOP::Add,
                    rd: tmp1,
                    rs1: tmp1.to_reg(),
                    rs2: tmp2.to_reg(),
                };
                inst.emit(&[], code, emit_info, state);

                // Jump to the middle of the jump table.
                // We add a 12 byte offset here, since there are 3 instructions since the AddPcUi.
                let inst = MInst::Jump {
                    link: zero_w(),
                    base: tmp1.to_reg(),
                    offset: Imm15::new(12).unwrap(),
                };
                inst.emit(&[], code, emit_info, state);

                // Emit the jump table:
                // Each entry in the jump table is 1 instruction, so 4 bytes.

                // Check if we need to emit an island
                let distance = (targets.len() * 4) as u32;
                if code.island_needed(distance) {
                    code.emit_island(distance);
                }

                // Emit the jumps back to back
                for target in targets.iter().copied() {
                    let inst = MInst::JumpRel { target };
                    inst.emit(&[], code, emit_info, state);
                }

                // We've just emitted an island that is safe up to *here*.
                // Mark it as such so that we don't needlessly emit additional islands.
                start_offset = code.cur_offset();
            }
        }

        let end_offset = code.cur_offset();
        assert!(
            (end_offset - start_offset) <= MInst::worst_case_size(),
            "Inst:{:?} length:{} worst_case_size:{}",
            self,
            end_offset - start_offset,
            MInst::worst_case_size()
        );
    }

    fn pretty_print_inst(&self, allocs: &[regalloc2::Allocation], state: &mut Self::State) -> String {
        let mut allocs = AllocationConsumer::new(allocs);
        self.print_with_state(state, &mut allocs)
    }
}
