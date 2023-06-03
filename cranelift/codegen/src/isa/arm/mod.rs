//! ARM 32-bit Instruction Set Architecture.

use crate::dominator_tree::DominatorTree;
use crate::ir::{Function, Type};
use crate::isa::arm::settings as arm_settings;
#[cfg(feature = "unwind")]
use crate::isa::unwind::systemv;
use crate::isa::{Builder as IsaBuilder, FunctionAlignment, TargetIsa};
use crate::machinst::{
    compile, CompiledCode, CompiledCodeStencil, MachInst, MachTextSectionBuilder, Reg, SigSet,
    TextSectionBuilder, VCode,
};
use crate::result::CodegenResult;
use crate::settings as shared_settings;
use alloc::{boxed::Box, vec::Vec};
use core::fmt;
use cranelift_control::ControlPlane;
use regalloc2::MachineEnv;
use target_lexicon::{Architecture, ArmArchitecture, Triple};

// New backend:
mod abi;
pub mod inst;
mod lower;
pub mod settings;

use inst::{create_reg_env, EmitInfo};

/// An ARM backend.
pub struct ArmBackend {
    triple: Triple,
    flags: shared_settings::Flags,
    isa_flags: arm_settings::Flags,
    machine_env: MachineEnv,
}

impl ArmBackend {
    /// Create a new ARM backend with the given (shared) flags.
    pub fn new_with_flags(
        triple: Triple,
        flags: shared_settings::Flags,
        isa_flags: arm_settings::Flags,
    ) -> ArmBackend {
        let machine_env = create_reg_env(&flags);
        ArmBackend {
            triple,
            flags,
            isa_flags,
            machine_env,
        }
    }

    /// This performs lowering to VCode, register-allocates the code, computes block layout and
    /// finalizes branches. The result is ready for binary emission.
    fn compile_vcode(
        &self,
        func: &Function,
        domtree: &DominatorTree,
        ctrl_plane: &mut ControlPlane,
    ) -> CodegenResult<(VCode<inst::Inst>, regalloc2::Output)> {
        let emit_info = EmitInfo::new(self.flags.clone());
        let sigs = SigSet::new::<abi::ArmMachineDeps>(func, &self.flags)?;
        let abi = abi::ArmCallee::new(func, self, &self.isa_flags, &sigs)?;
        compile::compile::<ArmBackend>(func, domtree, self, abi, emit_info, sigs, ctrl_plane)
    }
}

impl TargetIsa for ArmBackend {
    fn compile_function(
        &self,
        func: &Function,
        domtree: &DominatorTree,
        want_disasm: bool,
        ctrl_plane: &mut ControlPlane,
    ) -> CodegenResult<CompiledCodeStencil> {
        let (vcode, regalloc_result) = self.compile_vcode(func, domtree, ctrl_plane)?;

        let emit_result = vcode.emit(&regalloc_result, want_disasm, &self.flags, ctrl_plane);
        let frame_size = emit_result.frame_size;
        let value_labels_ranges = emit_result.value_labels_ranges;
        let buffer = emit_result.buffer;
        let sized_stackslot_offsets = emit_result.sized_stackslot_offsets;
        let dynamic_stackslot_offsets = emit_result.dynamic_stackslot_offsets;

        if let Some(disasm) = emit_result.disasm.as_ref() {
            log::debug!("disassembly:\n{}", disasm);
        }

        Ok(CompiledCodeStencil {
            buffer,
            frame_size,
            vcode: emit_result.disasm,
            value_labels_ranges,
            sized_stackslot_offsets,
            dynamic_stackslot_offsets,
            bb_starts: emit_result.bb_offsets,
            bb_edges: emit_result.bb_edges,
        })
    }

    fn name(&self) -> &'static str {
        "arm"
    }

    fn triple(&self) -> &Triple {
        &self.triple
    }

    fn flags(&self) -> &shared_settings::Flags {
        &self.flags
    }

    fn machine_env(&self) -> &MachineEnv {
        &self.machine_env
    }

    fn isa_flags(&self) -> Vec<shared_settings::Value> {
        self.isa_flags.iter().collect()
    }

    fn is_branch_protection_enabled(&self) -> bool {
        false
    }

    fn dynamic_vector_bytes(&self, _dyn_ty: Type) -> u32 {
        todo!()
    }

    #[cfg(feature = "unwind")]
    fn emit_unwind_info(
        &self,
        result: &CompiledCode,
        kind: crate::machinst::UnwindInfoKind,
    ) -> CodegenResult<Option<crate::isa::unwind::UnwindInfo>> {
        Ok(None) // TODO: implement unwinding
    }

    #[cfg(feature = "unwind")]
    fn create_systemv_cie(&self) -> Option<gimli::write::CommonInformationEntry> {
        None // TODO: implement unwinding
    }

    fn text_section_builder(&self, num_funcs: usize) -> Box<dyn TextSectionBuilder> {
        Box::new(MachTextSectionBuilder::<inst::Inst>::new(num_funcs))
    }

    #[cfg(feature = "unwind")]
    fn map_regalloc_reg_to_dwarf(&self, reg: Reg) -> Result<u16, systemv::RegisterMappingError> {
        Err(systemv::RegisterMappingError::UnsupportedArchitecture) // TODO: implement unwinding
    }

    fn function_alignment(&self) -> FunctionAlignment {
        inst::Inst::function_alignment()
    }

    #[cfg(feature = "disas")]
    fn to_capstone(&self) -> Result<capstone::Capstone, capstone::Error> {
        use capstone::prelude::*;
        let mut cs = Capstone::new()
            .arm()
            .mode(arch::arm::ArchMode::Arm)
            .build()?;
        // ARM uses inline constants rather than a separate constant pool right now.
        // Without this option, Capstone will stop disassembling as soon as it sees
        // an inline constant that is not also a valid instruction. With this option,
        // Capstone will print a `.byte` directive with the bytes of the inline constant
        // and continue to the next instruction.
        cs.set_skipdata(true)?;
        Ok(cs)
    }

    fn has_native_fma(&self) -> bool {
        todo!()
    }

    fn has_x86_blendv_lowering(&self, _: Type) -> bool {
        false
    }
}

impl fmt::Display for ArmBackend {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("MachBackend")
            .field("name", &self.name())
            .field("triple", &self.triple())
            .field("flags", &format!("{}", self.flags()))
            .finish()
    }
}

/// Create a new `isa::Builder`.
pub fn isa_builder(triple: Triple) -> IsaBuilder {
    assert!(triple.architecture == Architecture::Arm(ArmArchitecture::Armv6));
    IsaBuilder {
        triple,
        setup: arm_settings::builder(),
        constructor: |triple, shared_flags, builder| {
            let isa_flags = arm_settings::Flags::new(&shared_flags, builder);
            let backend = ArmBackend::new_with_flags(triple, shared_flags, isa_flags);
            Ok(backend.wrapped())
        },
    }
}
