//! Naming well-known routines in the runtime library.

use crate::{
    ir::{types, AbiParam, ExternalName, FuncRef, Function, Signature},
    isa::CallConv,
};
use core::fmt;
use core::str::FromStr;
#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// The name of a runtime library routine.
///
/// Runtime library calls are generated for Cranelift IR instructions that don't have an equivalent
/// ISA instruction or an easy macro expansion. A `LibCall` is used as a well-known name to refer to
/// the runtime library routine. This way, Cranelift doesn't have to know about the naming
/// convention in the embedding VM's runtime library.
///
/// This list is likely to grow over time.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum LibCall {
    /// probe for stack overflow. These are emitted for functions which need
    /// when the `enable_probestack` setting is true.
    Probestack,
    /// ceil.f32
    CeilF32,
    /// ceil.f64
    CeilF64,
    /// floor.f32
    FloorF32,
    /// floor.f64
    FloorF64,
    /// trunc.f32
    TruncF32,
    /// frunc.f64
    TruncF64,
    /// nearest.f32
    NearestF32,
    /// nearest.f64
    NearestF64,
    /// fma.f32
    FmaF32,
    /// fma.f64
    FmaF64,
    /// libc.memcpy
    Memcpy,
    /// libc.memset
    Memset,
    /// libc.memmove
    Memmove,
    /// libc.memcmp
    Memcmp,

    /// Unsigned 32 bit division
    UDiv32,
    /// Signed 32 bit division
    SDiv32,
    /// Unsigned 32 bit remainder
    URem32,
    /// Signed 32 bit remainder
    SRem32,
    /// Unsigned 64 bit division
    UDiv64,
    /// Signed 64 bit division
    SDiv64,
    /// Unsigned 64 bit remainder
    URem64,
    /// Signed 64 bit remainder
    SRem64,
    /// 32 bit pop-count
    PopCnt32,
    /// 64 bit pop-count
    PopCnt64,
    /// 32 bit count leading zeros
    Clz32,
    /// 64 bit count leading zeros
    Clz64,
    /// 32 bit count trailing zeros
    Ctz32,
    /// 64 bit count trailing zeros
    Ctz64,
    /// 32 bit count leading sign bits
    Cls32,
    /// 64 bit count leading sign bits
    Cls64,
    /// 32 bit bit-reverse
    Brev32,
    /// 64 bit bit-reverse
    Brev64,

    /// Elf __tls_get_addr
    ElfTlsGetAddr,
    /// Elf __tls_get_offset
    ElfTlsGetOffset,
    // When adding a new variant make sure to add it to `all_libcalls` too.
}

impl fmt::Display for LibCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl FromStr for LibCall {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Probestack" => Ok(Self::Probestack),
            "CeilF32" => Ok(Self::CeilF32),
            "CeilF64" => Ok(Self::CeilF64),
            "FloorF32" => Ok(Self::FloorF32),
            "FloorF64" => Ok(Self::FloorF64),
            "TruncF32" => Ok(Self::TruncF32),
            "TruncF64" => Ok(Self::TruncF64),
            "NearestF32" => Ok(Self::NearestF32),
            "NearestF64" => Ok(Self::NearestF64),
            "FmaF32" => Ok(Self::FmaF32),
            "FmaF64" => Ok(Self::FmaF64),
            "Memcpy" => Ok(Self::Memcpy),
            "Memset" => Ok(Self::Memset),
            "Memmove" => Ok(Self::Memmove),
            "Memcmp" => Ok(Self::Memcmp),

            "UDiv32" => Ok(Self::UDiv32),
            "SDiv32" => Ok(Self::SDiv32),
            "URem32" => Ok(Self::URem32),
            "SRem32" => Ok(Self::SRem32),
            "UDiv64" => Ok(Self::UDiv64),
            "SDiv64" => Ok(Self::SDiv64),
            "URem64" => Ok(Self::URem64),
            "SRem64" => Ok(Self::SRem64),
            "PopCnt32" => Ok(Self::PopCnt32),
            "PopCnt64" => Ok(Self::PopCnt64),
            "Clz32" => Ok(Self::Clz32),
            "Clz64" => Ok(Self::Clz64),
            "Ctz32" => Ok(Self::Ctz32),
            "Ctz64" => Ok(Self::Ctz64),
            "Cls32" => Ok(Self::Cls32),
            "Cls64" => Ok(Self::Cls64),
            "Brev32" => Ok(Self::Brev32),
            "Brev64" => Ok(Self::Brev64),

            "ElfTlsGetAddr" => Ok(Self::ElfTlsGetAddr),
            "ElfTlsGetOffset" => Ok(Self::ElfTlsGetOffset),
            _ => Err(()),
        }
    }
}

impl LibCall {
    /// Get a list of all known `LibCall`'s.
    pub fn all_libcalls() -> &'static [LibCall] {
        use LibCall::*;
        &[
            Probestack,
            CeilF32,
            CeilF64,
            FloorF32,
            FloorF64,
            TruncF32,
            TruncF64,
            NearestF32,
            NearestF64,
            FmaF32,
            FmaF64,
            Memcpy,
            Memset,
            Memmove,
            Memcmp,
            UDiv32,
            SDiv32,
            URem32,
            SRem32,
            UDiv64,
            SDiv64,
            URem64,
            SRem64,
            PopCnt32,
            PopCnt64,
            Clz32,
            Clz64,
            Ctz32,
            Ctz64,
            Cls32,
            Cls64,
            Brev32,
            Brev64,
            ElfTlsGetAddr,
            ElfTlsGetOffset,
        ]
    }

    /// Get a [Signature] for the function targeted by this [LibCall].
    pub fn signature(&self, call_conv: CallConv) -> Signature {
        use types::*;
        let mut sig = Signature::new(call_conv);

        match self {
            LibCall::CeilF32 | LibCall::FloorF32 | LibCall::TruncF32 | LibCall::NearestF32 => {
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::TruncF64 | LibCall::FloorF64 | LibCall::CeilF64 | LibCall::NearestF64 => {
                sig.params.push(AbiParam::new(F64));
                sig.returns.push(AbiParam::new(F64));
            }
            LibCall::FmaF32 | LibCall::FmaF64 => {
                let ty = if *self == LibCall::FmaF32 { F32 } else { F64 };

                sig.params.push(AbiParam::new(ty));
                sig.params.push(AbiParam::new(ty));
                sig.params.push(AbiParam::new(ty));
                sig.returns.push(AbiParam::new(ty));
            }
            LibCall::UDiv32 | LibCall::URem32 => {
                sig.params.push(AbiParam::new(I32).uext());
                sig.params.push(AbiParam::new(I32).uext());
                sig.returns.push(AbiParam::new(I32).uext());
            }
            LibCall::SDiv32 | LibCall::SRem32 => {
                sig.params.push(AbiParam::new(I32).sext());
                sig.params.push(AbiParam::new(I32).sext());
                sig.returns.push(AbiParam::new(I32).sext());
            }
            LibCall::UDiv64 | LibCall::URem64 => {
                sig.params.push(AbiParam::new(I64).uext());
                sig.params.push(AbiParam::new(I64).uext());
                sig.returns.push(AbiParam::new(I64).uext());
            }
            LibCall::SDiv64 | LibCall::SRem64 => {
                sig.params.push(AbiParam::new(I64).sext());
                sig.params.push(AbiParam::new(I64).sext());
                sig.returns.push(AbiParam::new(I64).sext());
            }
            LibCall::PopCnt32 | LibCall::Clz32 | LibCall::Ctz32 | LibCall::Brev32 => {
                sig.params.push(AbiParam::new(I32).uext());
                sig.returns.push(AbiParam::new(I32).uext());
            }
            LibCall::Cls32 => {
                sig.params.push(AbiParam::new(I32).sext());
                sig.returns.push(AbiParam::new(I32).sext());
            }
            LibCall::PopCnt64 | LibCall::Clz64 | LibCall::Ctz64 | LibCall::Brev64 => {
                sig.params.push(AbiParam::new(I64).uext());
                sig.returns.push(AbiParam::new(I64).uext());
            }
            LibCall::Cls64 => {
                sig.params.push(AbiParam::new(I64).sext());
                sig.returns.push(AbiParam::new(I64).sext());
            }
            LibCall::Probestack
            | LibCall::Memcpy
            | LibCall::Memset
            | LibCall::Memmove
            | LibCall::Memcmp
            | LibCall::ElfTlsGetAddr
            | LibCall::ElfTlsGetOffset => unimplemented!(),
        }

        sig
    }
}

/// Get a function reference for the probestack function in `func`.
///
/// If there is an existing reference, use it, otherwise make a new one.
pub fn get_probestack_funcref(func: &mut Function) -> Option<FuncRef> {
    find_funcref(LibCall::Probestack, func)
}

/// Get the existing function reference for `libcall` in `func` if it exists.
fn find_funcref(libcall: LibCall, func: &Function) -> Option<FuncRef> {
    // We're assuming that all libcall function decls are at the end.
    // If we get this wrong, worst case we'll have duplicate libcall decls which is harmless.
    for (fref, func_data) in func.dfg.ext_funcs.iter().rev() {
        match func_data.name {
            ExternalName::LibCall(lc) => {
                if lc == libcall {
                    return Some(fref);
                }
            }
            _ => break,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn display() {
        assert_eq!(LibCall::CeilF32.to_string(), "CeilF32");
        assert_eq!(LibCall::NearestF64.to_string(), "NearestF64");
    }

    #[test]
    fn parsing() {
        assert_eq!("FloorF32".parse(), Ok(LibCall::FloorF32));
    }

    #[test]
    fn all_libcalls_to_from_string() {
        for &libcall in LibCall::all_libcalls() {
            assert_eq!(libcall.to_string().parse(), Ok(libcall));
        }
    }
}
