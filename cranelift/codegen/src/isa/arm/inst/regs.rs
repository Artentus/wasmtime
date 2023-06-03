//! ARM ISA definitions: registers.

use crate::settings;
use regalloc2::MachineEnv;

/// Create the register environment for ARM.
pub fn create_reg_env(flags: &settings::Flags) -> MachineEnv {
    MachineEnv {
        preferred_regs_by_class: [
            vec![],
            vec![],
            // Vector Regclass is unused
            vec![],
        ],
        non_preferred_regs_by_class: [
            vec![],
            vec![],
            // Vector Regclass is unused
            vec![],
        ],
        scratch_by_class: [None, None, None],
        fixed_stack_slots: vec![],
    }
}
