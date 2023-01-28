//! Lowering rules for A32.
use crate::ir::{Inst, LibCall, ExternalName};
use crate::isa::a32::abi::*;
use crate::isa::a32::inst::MInst;
use crate::isa::a32::A32Backend;
use crate::isa::CallConv;
use crate::machinst::*;
use crate::settings::Flags;
use crate::result::CodegenResult;
use target_lexicon::Triple;
use smallvec::smallvec;

pub mod isle;

//=============================================================================
// Lowering-backend trait implementation.

impl LowerBackend for A32Backend {
    type MInst = MInst;

    fn lower(&self, ctx: &mut Lower<Self::MInst>, inst: Inst) -> Option<InstOutput> {
        isle::lower(ctx, self, inst)
    }

    fn lower_branch(
        &self,
        ctx: &mut Lower<Self::MInst>,
        inst: Inst,
        targets: &[MachLabel],
    ) -> Option<()> {
        isle::lower_branch(ctx, self, inst, targets)
    }
}

fn emit_vm_call(
    ctx: &mut Lower<MInst>,
    flags: &Flags,
    triple: &Triple,
    libcall: LibCall,
    inputs: &[ValueRegs<Reg>],
    outputs: &[ValueRegs<Writable<Reg>>],
) -> CodegenResult<()> {
    let extname = ExternalName::LibCall(libcall);

    // TODO avoid recreating signatures for every single Libcall function.
    let call_conv = CallConv::for_libcall(flags, CallConv::triple_default(triple));
    let sig = libcall.signature(call_conv);
    let caller_conv = ctx.abi().call_conv(ctx.sigs());

    if !ctx.sigs().have_abi_sig_for_signature(&sig) {
        ctx.sigs_mut()
            .make_abi_sig_from_ir_signature::<A32MachineDeps>(sig.clone(), flags)?;
    }

    let mut abi =
        A32ABICaller::from_libcall(ctx.sigs(), &sig, &extname, RelocDistance::Far, caller_conv, flags.clone())?;

    abi.emit_stack_pre_adjust(ctx);

    assert_eq!(inputs.len(), abi.num_args(ctx.sigs()));

    for (i, input) in inputs.iter().enumerate() {
        for inst in abi.gen_arg(ctx, i, *input) {
            ctx.emit(inst);
        }
    }

    let mut retval_insts: SmallInstVec<_> = smallvec![];
    for (i, output) in outputs.iter().enumerate() {
        retval_insts.extend(abi.gen_retval(ctx, i, *output).into_iter());
    }
    abi.emit_call(ctx);
    for inst in retval_insts {
        ctx.emit(inst);
    }
    abi.emit_stack_post_adjust(ctx);

    Ok(())
}
