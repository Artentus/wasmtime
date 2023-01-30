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
    /// 128 bit left shift
    Shl128,
    /// Unsigned 128 bit right shift
    UShr128,
    /// Signed 128 bit right shift
    SShr128,
    /// 128 bit rotating left shift
    Rotl128,
    /// 128 bit rotating right shift
    Rotr128,
    /// 128 bit multiplication
    Mul128,
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
    /// Unsigned 128 bit division
    UDiv128,
    /// Signed 128 bit division
    SDiv128,
    /// Unsigned 128 bit remainder
    URem128,
    /// Signed 128 bit remainder
    SRem128,
    /// 32 bit pop-count
    PopCnt32,
    /// 64 bit pop-count
    PopCnt64,
    /// 128 bit pop-count
    PopCnt128,
    /// 32 bit count leading zeros
    Clz32,
    /// 64 bit count leading zeros
    Clz64,
    /// 128 bit count leading zeros
    Clz128,
    /// 32 bit count trailing zeros
    Ctz32,
    /// 64 bit count trailing zeros
    Ctz64,
    /// 128 bit count trailing zeros
    Ctz128,
    /// 32 bit count leading sign bits
    Cls32,
    /// 64 bit count leading sign bits
    Cls64,
    /// 128 bit count leading sign bits
    Cls128,
    /// 32 bit bit-reverse
    Brev32,
    /// 64 bit bit-reverse
    Brev64,
    /// 128 bit bit-reverse
    Brev128,

    /// add.f32
    AddF32,
    /// add.f64
    AddF64,
    /// sub.f32
    SubF32,
    /// sub.f64
    SubF64,
    /// mul.f32
    MulF32,
    /// mul.f64
    MulF64,
    /// div.f32
    DivF32,
    /// div.f64
    DivF64,
    /// min.f32
    MinF32,
    /// min.f64
    MinF64,
    /// max.f32
    MaxF32,
    /// max.f64
    MaxF64,
    /// copysign.f32
    CopySignF32,
    /// copysign.f64
    CopySignF64,
    /// neg.f32
    NegF32,
    /// neg.f64
    NegF64,
    /// abs.f32
    AbsF32,
    /// abs.f64
    AbsF64,
    /// sqrt.f32
    SqrtF32,
    /// sqrt.f64
    SqrtF64,
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
    /// promote
    Promote,
    /// demote
    Demote,
    /// cmp.f32
    CmpF32,
    /// cmp.f64
    CmpF64,

    /// fcvt_to_uint.i32
    CvtF32U32,
    /// fcvt_to_sint.i32
    CvtF32S32,
    /// fcvt_to_uint.i64
    CvtF32U64,
    /// fcvt_to_sint.i64
    CvtF32S64,
    /// fcvt_to_uint.i32
    CvtF64U32,
    /// fcvt_to_sint.i32
    CvtF64S32,
    /// fcvt_to_uint.i64
    CvtF64U64,
    /// fcvt_to_sint.i64
    CvtF64S64,
    /// fcvt_to_uint_sat.i32
    CvtF32U32Sat,
    /// fcvt_to_sint_sat.i32
    CvtF32S32Sat,
    /// fcvt_to_uint_sat.i64
    CvtF32U64Sat,
    /// fcvt_to_sint_sat.i64
    CvtF32S64Sat,
    /// fcvt_to_uint_sat.i32
    CvtF64U32Sat,
    /// fcvt_to_sint_sat.i32
    CvtF64S32Sat,
    /// fcvt_to_uint_sat.i64
    CvtF64U64Sat,
    /// fcvt_to_sint_sat.i64
    CvtF64S64Sat,
    /// fcvt_from_uint.f32
    CvtU32F32,
    /// fcvt_from_sint.f32
    CvtS32F32,
    /// fcvt_from_uint.f32
    CvtU64F32,
    /// fcvt_from_sint.f32
    CvtS64F32,
    /// fcvt_from_uint.f64
    CvtU32F64,
    /// fcvt_from_sint.f64
    CvtS32F64,
    /// fcvt_from_uint.f64
    CvtU64F64,
    /// fcvt_from_sint.f64
    CvtS64F64,

    /// probe for stack overflow. These are emitted for functions which need
    /// when the `enable_probestack` setting is true.
    Probestack,

    /// libc.memcpy
    Memcpy,
    /// libc.memset
    Memset,
    /// libc.memmove
    Memmove,
    /// libc.memcmp
    Memcmp,

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
            "Shl128" => Ok(Self::Shl128),
            "UShr128" => Ok(Self::UShr128),
            "SShr128" => Ok(Self::SShr128),
            "Rotl128" => Ok(Self::Rotl128),
            "Rotr128" => Ok(Self::Rotr128),
            "Mul128" => Ok(Self::Mul128),
            "UDiv32" => Ok(Self::UDiv32),
            "SDiv32" => Ok(Self::SDiv32),
            "URem32" => Ok(Self::URem32),
            "SRem32" => Ok(Self::SRem32),
            "UDiv64" => Ok(Self::UDiv64),
            "SDiv64" => Ok(Self::SDiv64),
            "URem64" => Ok(Self::URem64),
            "SRem64" => Ok(Self::SRem64),
            "UDiv128" => Ok(Self::UDiv128),
            "SDiv128" => Ok(Self::SDiv128),
            "URem128" => Ok(Self::URem128),
            "SRem128" => Ok(Self::SRem128),
            "PopCnt32" => Ok(Self::PopCnt32),
            "PopCnt64" => Ok(Self::PopCnt64),
            "PopCnt128" => Ok(Self::PopCnt128),
            "Clz32" => Ok(Self::Clz32),
            "Clz64" => Ok(Self::Clz64),
            "Clz128" => Ok(Self::Clz128),
            "Ctz32" => Ok(Self::Ctz32),
            "Ctz64" => Ok(Self::Ctz64),
            "Ctz128" => Ok(Self::Ctz128),
            "Cls32" => Ok(Self::Cls32),
            "Cls64" => Ok(Self::Cls64),
            "Cls128" => Ok(Self::Cls128),
            "Brev32" => Ok(Self::Brev32),
            "Brev64" => Ok(Self::Brev64),
            "Brev128" => Ok(Self::Brev128),

            "AddF32" => Ok(Self::AddF32),
            "AddF64" => Ok(Self::AddF64),
            "SubF32" => Ok(Self::SubF32),
            "SubF64" => Ok(Self::SubF64),
            "MulF32" => Ok(Self::MulF32),
            "MulF64" => Ok(Self::MulF64),
            "DivF32" => Ok(Self::DivF32),
            "DivF64" => Ok(Self::DivF64),
            "MinF32" => Ok(Self::MinF32),
            "MinF64" => Ok(Self::MinF64),
            "MaxF32" => Ok(Self::MaxF32),
            "MaxF64" => Ok(Self::MaxF64),
            "CopySignF32" => Ok(Self::CopySignF32),
            "CopySignF64" => Ok(Self::CopySignF64),
            "NegF32" => Ok(Self::NegF32),
            "NegF64" => Ok(Self::NegF64),
            "AbsF32" => Ok(Self::AbsF32),
            "AbsF64" => Ok(Self::AbsF64),
            "SqrtF32" => Ok(Self::SqrtF32),
            "SqrtF64" => Ok(Self::SqrtF64),
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
            "Promote" => Ok(Self::Promote),
            "Demote" => Ok(Self::Demote),
            "CmpF32" => Ok(Self::CmpF32),
            "CmpF64" => Ok(Self::CmpF64),

            "CvtF32U32" => Ok(Self::CvtF32U32),
            "CvtF32S32" => Ok(Self::CvtF32S32),
            "CvtF32U64" => Ok(Self::CvtF32U64),
            "CvtF32S64" => Ok(Self::CvtF32S64),
            "CvtF64U32" => Ok(Self::CvtF64U32),
            "CvtF64S32" => Ok(Self::CvtF64S32),
            "CvtF64U64" => Ok(Self::CvtF64U64),
            "CvtF64S64" => Ok(Self::CvtF64S64),
            "CvtF32U32Sat" => Ok(Self::CvtF32U32Sat),
            "CvtF32S32Sat" => Ok(Self::CvtF32S32Sat),
            "CvtF32U64Sat" => Ok(Self::CvtF32U64Sat),
            "CvtF32S64Sat" => Ok(Self::CvtF32S64Sat),
            "CvtF64U32Sat" => Ok(Self::CvtF64U32Sat),
            "CvtF64S32Sat" => Ok(Self::CvtF64S32Sat),
            "CvtF64U64Sat" => Ok(Self::CvtF64U64Sat),
            "CvtF64S64Sat" => Ok(Self::CvtF64S64Sat),
            "CvtU32F32" => Ok(Self::CvtU32F32),
            "CvtS32F32" => Ok(Self::CvtS32F32),
            "CvtU64F32" => Ok(Self::CvtU64F32),
            "CvtS64F32" => Ok(Self::CvtS64F32),
            "CvtU32F64" => Ok(Self::CvtU32F64),
            "CvtS32F64" => Ok(Self::CvtS32F64),
            "CvtU64F64" => Ok(Self::CvtU64F64),
            "CvtS64F64" => Ok(Self::CvtS64F64),

            "Probestack" => Ok(Self::Probestack),

            "Memcpy" => Ok(Self::Memcpy),
            "Memset" => Ok(Self::Memset),
            "Memmove" => Ok(Self::Memmove),
            "Memcmp" => Ok(Self::Memcmp),

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
            Shl128,
            UShr128,
            SShr128,
            Rotl128,
            Rotr128,
            Mul128,
            UDiv32,
            SDiv32,
            URem32,
            SRem32,
            UDiv64,
            SDiv64,
            URem64,
            SRem64,
            UDiv128,
            SDiv128,
            URem128,
            SRem128,
            PopCnt32,
            PopCnt64,
            PopCnt128,
            Clz32,
            Clz64,
            Clz128,
            Ctz32,
            Ctz64,
            Ctz128,
            Cls32,
            Cls64,
            Cls128,
            Brev32,
            Brev64,
            Brev128,

            AddF32,
            AddF64,
            SubF32,
            SubF64,
            MulF32,
            MulF64,
            DivF32,
            DivF64,
            MinF32,
            MinF64,
            MaxF32,
            MaxF64,
            CopySignF32,
            CopySignF64,
            NegF32,
            NegF64,
            AbsF32,
            AbsF64,
            SqrtF32,
            SqrtF64,
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
            Promote,
            Demote,
            CmpF32,
            CmpF64,

            CvtF32U32,
            CvtF32S32,
            CvtF32U64,
            CvtF32S64,
            CvtF64U32,
            CvtF64S32,
            CvtF64U64,
            CvtF64S64,
            CvtF32U32Sat,
            CvtF32S32Sat,
            CvtF32U64Sat,
            CvtF32S64Sat,
            CvtF64U32Sat,
            CvtF64S32Sat,
            CvtF64U64Sat,
            CvtF64S64Sat,
            CvtU32F32,
            CvtS32F32,
            CvtU64F32,
            CvtS64F32,
            CvtU32F64,
            CvtS32F64,
            CvtU64F64,
            CvtS64F64,

            Probestack,
            Memcpy,
            Memset,
            Memmove,
            Memcmp,
            ElfTlsGetAddr,
            ElfTlsGetOffset,
        ]
    }

    /// Get a [Signature] for the function targeted by this [LibCall].
    pub fn signature(&self, call_conv: CallConv) -> Signature {
        use types::*;
        let mut sig = Signature::new(call_conv);

        match self {
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
            LibCall::UDiv128 | LibCall::URem128 => {
                sig.params.push(AbiParam::new(I128).uext());
                sig.params.push(AbiParam::new(I128).uext());
                sig.returns.push(AbiParam::new(I128).uext());
            }
            LibCall::SDiv128 | LibCall::SRem128 | LibCall::Mul128 => {
                sig.params.push(AbiParam::new(I128).sext());
                sig.params.push(AbiParam::new(I128).sext());
                sig.returns.push(AbiParam::new(I128).sext());
            }
            LibCall::Shl128 | LibCall::UShr128 | LibCall::Rotl128 | LibCall::Rotr128 => {
                sig.params.push(AbiParam::new(I128).uext());
                sig.params.push(AbiParam::new(I8));
                sig.returns.push(AbiParam::new(I128).uext());
            }
            LibCall::SShr128 => {
                sig.params.push(AbiParam::new(I128).sext());
                sig.params.push(AbiParam::new(I8));
                sig.returns.push(AbiParam::new(I128).sext());
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
            LibCall::PopCnt128 | LibCall::Clz128 | LibCall::Ctz128 | LibCall::Brev128 => {
                sig.params.push(AbiParam::new(I128).uext());
                sig.returns.push(AbiParam::new(I128).uext());
            }
            LibCall::Cls128 => {
                sig.params.push(AbiParam::new(I128).sext());
                sig.returns.push(AbiParam::new(I128).sext());
            }

            LibCall::AddF32
            | LibCall::SubF32
            | LibCall::MulF32
            | LibCall::DivF32
            | LibCall::MinF32
            | LibCall::MaxF32
            | LibCall::CopySignF32 => {
                sig.params.push(AbiParam::new(F32));
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::AddF64
            | LibCall::SubF64
            | LibCall::MulF64
            | LibCall::DivF64
            | LibCall::MinF64
            | LibCall::MaxF64
            | LibCall::CopySignF64 => {
                sig.params.push(AbiParam::new(F64));
                sig.params.push(AbiParam::new(F64));
                sig.returns.push(AbiParam::new(F64));
            }
            LibCall::NegF32
            | LibCall::AbsF32
            | LibCall::SqrtF32
            | LibCall::CeilF32
            | LibCall::FloorF32
            | LibCall::TruncF32
            | LibCall::NearestF32 => {
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::NegF64
            | LibCall::AbsF64
            | LibCall::SqrtF64
            | LibCall::CeilF64
            | LibCall::FloorF64
            | LibCall::TruncF64
            | LibCall::NearestF64 => {
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
            LibCall::Promote => {
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(F64));
            }
            LibCall::Demote => {
                sig.params.push(AbiParam::new(F64));
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::CmpF32 => {
                sig.params.push(AbiParam::new(F32));
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(I8));
            }
            LibCall::CmpF64 => {
                sig.params.push(AbiParam::new(F64));
                sig.params.push(AbiParam::new(F64));
                sig.returns.push(AbiParam::new(I8));
            }

            LibCall::CvtF32U32
            | LibCall::CvtF32U32Sat
            | LibCall::CvtF32S32
            | LibCall::CvtF32S32Sat => {
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(I32));
            }
            LibCall::CvtF32U64
            | LibCall::CvtF32U64Sat
            | LibCall::CvtF32S64
            | LibCall::CvtF32S64Sat => {
                sig.params.push(AbiParam::new(F32));
                sig.returns.push(AbiParam::new(I64));
            }
            LibCall::CvtF64U32
            | LibCall::CvtF64U32Sat
            | LibCall::CvtF64S32
            | LibCall::CvtF64S32Sat => {
                sig.params.push(AbiParam::new(F64));
                sig.returns.push(AbiParam::new(I32));
            }
            LibCall::CvtF64U64
            | LibCall::CvtF64U64Sat
            | LibCall::CvtF64S64
            | LibCall::CvtF64S64Sat => {
                sig.params.push(AbiParam::new(F64));
                sig.returns.push(AbiParam::new(I64));
            }
            LibCall::CvtU32F32 => {
                sig.params.push(AbiParam::new(I32).uext());
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::CvtS32F32 => {
                sig.params.push(AbiParam::new(I32).sext());
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::CvtU64F32 => {
                sig.params.push(AbiParam::new(I64).uext());
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::CvtS64F32 => {
                sig.params.push(AbiParam::new(I64).sext());
                sig.returns.push(AbiParam::new(F32));
            }
            LibCall::CvtU32F64 => {
                sig.params.push(AbiParam::new(I32).uext());
                sig.returns.push(AbiParam::new(F64));
            }
            LibCall::CvtS32F64 => {
                sig.params.push(AbiParam::new(I32).sext());
                sig.returns.push(AbiParam::new(F64));
            }
            LibCall::CvtU64F64 => {
                sig.params.push(AbiParam::new(I64).uext());
                sig.returns.push(AbiParam::new(F64));
            }
            LibCall::CvtS64F64 => {
                sig.params.push(AbiParam::new(I64).sext());
                sig.returns.push(AbiParam::new(F64));
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
