//! ARM ISA definitions: instruction arguments.

use crate::isa::arm::inst::*;
use crate::machinst::{MachLabel, PrettyPrint};
use std::string::String;

//=============================================================================
// Instruction sub-components (conditions, branches and branch targets):
// definitions

/// A branch target. Either unresolved (basic-block index) or resolved (offset
/// from end of current instruction).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchTarget {
    /// An unresolved reference to a Label.
    Label(MachLabel),
    /// A fixed PC offset.
    ResolvedOffset(i32),
}

impl PrettyPrint for BranchTarget {
    fn pretty_print(&self, _: u8, _: &mut AllocationConsumer<'_>) -> String {
        match self {
            &BranchTarget::Label(label) => format!("label{:?}", label.get()),
            &BranchTarget::ResolvedOffset(off) => format!("{}", off),
        }
    }
}
