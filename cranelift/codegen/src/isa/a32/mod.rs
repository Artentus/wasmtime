//! A32 Instruction Set Architecture.

use crate::ir;
use crate::ir::condcodes::IntCC;
use crate::ir::Function;

use crate::isa::a32::settings as a32_settings;
use crate::isa::{Builder as IsaBuilder, TargetIsa};
use crate::machinst::{
    compile, CompiledCode, CompiledCodeStencil, MachTextSectionBuilder, Reg, SigSet,
    TextSectionBuilder, VCode,
};
use crate::result::CodegenResult;
use crate::settings as shared_settings;
use alloc::{boxed::Box, vec::Vec};
use core::fmt;
use regalloc2::MachineEnv;
use target_lexicon::{Architecture, Triple};
mod abi;
pub(crate) mod inst;
mod lower;
mod settings;
#[cfg(feature = "unwind")]
use crate::isa::unwind::systemv;

use inst::create_reg_environment;

use self::inst::EmitInfo;

/// An A32 backend.
pub struct A32Backend {
    triple: Triple,
    flags: shared_settings::Flags,
    isa_flags: a32_settings::Flags,
    mach_env: MachineEnv,
}

impl A32Backend {
    /// Create a new A32 backend with the given (shared) flags.
    pub fn new_with_flags(
        triple: Triple,
        flags: shared_settings::Flags,
        isa_flags: a32_settings::Flags,
    ) -> A32Backend {
        let mach_env = create_reg_environment(&flags);
        A32Backend {
            triple,
            flags,
            isa_flags,
            mach_env,
        }
    }

    /// This performs lowering to VCode, register-allocates the code, computes block layout and
    /// finalizes branches. The result is ready for binary emission.
    fn compile_vcode(
        &self,
        func: &Function,
    ) -> CodegenResult<(VCode<inst::MInst>, regalloc2::Output)> {
        let emit_info = EmitInfo::new(self.flags.clone(), self.isa_flags.clone());
        let sigs = SigSet::new::<abi::A32MachineDeps>(func, &self.flags)?;
        let abi = abi::A32Callee::new(func, self, &self.isa_flags, &sigs)?;
        compile::compile::<A32Backend>(func, self, abi, emit_info, sigs)
    }
}

impl fmt::Display for A32Backend {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("A32Backend")
            .field("name", &self.name())
            .field("triple", &self.triple())
            .field("flags", &format!("{}", self.flags()))
            .finish()
    }
}

impl TargetIsa for A32Backend {
    fn compile_function(
        &self,
        func: &Function,
        want_disasm: bool,
    ) -> CodegenResult<CompiledCodeStencil> {
        let (vcode, regalloc_result) = self.compile_vcode(func)?;

        let want_disasm = want_disasm || log::log_enabled!(log::Level::Debug);
        let emit_result = vcode.emit(
            &regalloc_result,
            want_disasm,
            self.flags.machine_code_cfg_info(),
        );
        let frame_size = emit_result.frame_size;
        let value_labels_ranges = emit_result.value_labels_ranges;
        let buffer = emit_result.buffer.finish();
        let sized_stackslot_offsets = emit_result.sized_stackslot_offsets;
        let dynamic_stackslot_offsets = emit_result.dynamic_stackslot_offsets;

        if let Some(disasm) = emit_result.disasm.as_ref() {
            log::debug!("disassembly:\n{}", disasm);
        }

        Ok(CompiledCodeStencil {
            buffer,
            frame_size,
            disasm: emit_result.disasm,
            value_labels_ranges,
            sized_stackslot_offsets,
            dynamic_stackslot_offsets,
            bb_starts: emit_result.bb_offsets,
            bb_edges: emit_result.bb_edges,
            alignment: emit_result.alignment,
        })
    }

    fn name(&self) -> &'static str {
        "a32"
    }
    fn dynamic_vector_bytes(&self, _dynamic_ty: ir::Type) -> u32 {
        4
    }

    fn triple(&self) -> &Triple {
        &self.triple
    }

    fn flags(&self) -> &shared_settings::Flags {
        &self.flags
    }

    fn machine_env(&self) -> &MachineEnv {
        &self.mach_env
    }

    fn isa_flags(&self) -> Vec<shared_settings::Value> {
        self.isa_flags.iter().collect()
    }

    fn unsigned_add_overflow_condition(&self) -> IntCC {
        IntCC::UnsignedGreaterThanOrEqual
    }

    #[cfg(feature = "unwind")]
    fn emit_unwind_info(
        &self,
        _result: &CompiledCode,
        _kind: crate::machinst::UnwindInfoKind,
    ) -> CodegenResult<Option<crate::isa::unwind::UnwindInfo>> {
        CodegenResult::Ok(None)
    }

    #[cfg(feature = "unwind")]
    fn create_systemv_cie(&self) -> Option<gimli::write::CommonInformationEntry> {
        None
    }

    fn text_section_builder(&self, num_funcs: usize) -> Box<dyn TextSectionBuilder> {
        Box::new(MachTextSectionBuilder::<inst::MInst>::new(num_funcs))
    }

    #[cfg(feature = "unwind")]
    fn map_regalloc_reg_to_dwarf(&self, _reg: Reg) -> Result<u16, systemv::RegisterMappingError> {
        Err(systemv::RegisterMappingError::UnsupportedArchitecture)
    }

    fn function_alignment(&self) -> u32 {
        4
    }
}

/// Create a new `isa::Builder`.
pub fn isa_builder(triple: Triple) -> IsaBuilder {
    match triple.architecture {
        Architecture::A32 => {}
        _ => unreachable!(),
    }

    IsaBuilder {
        triple,
        setup: a32_settings::builder(),
        constructor: |triple, shared_flags, builder| {
            let isa_flags = a32_settings::Flags::new(&shared_flags, builder);
            let backend = A32Backend::new_with_flags(triple, shared_flags, isa_flags);
            Ok(backend.wrapped())
        },
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::cursor::{Cursor, FuncCursor};
    use crate::ir::types::*;
    use crate::ir::{AbiParam, Function, InstBuilder, Signature, UserFuncName};
    use crate::isa::CallConv;
    use crate::settings;
    use crate::settings::Configurable;
    use core::str::FromStr;
    use target_lexicon::Triple;

    #[test]
    fn test_compile_function() {
        let name = UserFuncName::testcase("test0");
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(I32));
        sig.returns.push(AbiParam::new(I32));
        let mut func = Function::with_name_signature(name, sig);

        let bb0 = func.dfg.make_block();
        let arg0 = func.dfg.append_block_param(bb0, I32);

        let mut pos = FuncCursor::new(&mut func);
        pos.insert_block(bb0);
        let v0 = pos.ins().iconst(I32, 0x12345);
        let v1 = pos.ins().iadd(arg0, v0);
        pos.ins().return_(&[v1]);

        let mut shared_flags_builder = settings::builder();
        shared_flags_builder.set("opt_level", "none").unwrap();
        let shared_flags = settings::Flags::new(shared_flags_builder);
        let isa_flags = a32_settings::Flags::new(&shared_flags, a32_settings::builder());
        let backend = A32Backend::new_with_flags(
            Triple::from_str("a32").unwrap(),
            shared_flags,
            isa_flags,
        );

        //let (vcode, reg_alloc) = backend.compile_vcode(&func).unwrap();
        //panic!("{:?}", vcode);

        let buffer = backend.compile_function(&mut func, true).unwrap();
        let code = buffer.buffer.data();

        // 0:   40004344        ldui  a3, 0x12000
        // 4:   068A632A        or    a3, a3, 0x345
        // 8:   000C3181        add   a0, a0, a3
        // C:   00001004        jmp   ra

        let golden = vec![
            0x44, 0x43, 0x00, 0x40,
            0x2A, 0x63, 0x8A, 0x06,
            0x81, 0x31, 0x0C, 0x00,
            0x04, 0x10, 0x00, 0x00,
        ];
        assert_eq!(code, &golden[..]);
    }
}
