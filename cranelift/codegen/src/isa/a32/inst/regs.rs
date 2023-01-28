//! A32 ISA definitions: registers.

use crate::machinst::{Reg, Writable, RealReg};
use regalloc2::{MachineEnv, PReg, VReg, RegClass};

#[inline]
pub const fn p_reg(enc: usize) -> PReg {
    PReg::new(enc, RegClass::Int)
}

pub const P_ZERO: PReg = p_reg( 0);
pub const P_RA  : PReg = p_reg( 1);
pub const P_SP  : PReg = p_reg( 2);
pub const P_A0  : PReg = p_reg( 3);
pub const P_A1  : PReg = p_reg( 4);
pub const P_A2  : PReg = p_reg( 5);
pub const P_A3  : PReg = p_reg( 6);
pub const P_A4  : PReg = p_reg( 7);
pub const P_A5  : PReg = p_reg( 8);
pub const P_A6  : PReg = p_reg( 9);
pub const P_A7  : PReg = p_reg(10);
pub const P_T0  : PReg = p_reg(11);
pub const P_T1  : PReg = p_reg(12);
pub const P_T2  : PReg = p_reg(13);
pub const P_T3  : PReg = p_reg(14);
pub const P_T4  : PReg = p_reg(15);
pub const P_T5  : PReg = p_reg(16);
pub const P_T6  : PReg = p_reg(17);
pub const P_T7  : PReg = p_reg(18);
pub const P_S0  : PReg = p_reg(19);
pub const P_S1  : PReg = p_reg(20);
pub const P_S2  : PReg = p_reg(21);
pub const P_S3  : PReg = p_reg(22);
pub const P_S4  : PReg = p_reg(23);
pub const P_S5  : PReg = p_reg(24);
pub const P_S6  : PReg = p_reg(25);
pub const P_S7  : PReg = p_reg(26);
pub const P_S8  : PReg = p_reg(27);
pub const P_S9  : PReg = p_reg(28);
pub const P_S10 : PReg = p_reg(29);
pub const P_S11 : PReg = p_reg(30);
pub const P_S12 : PReg = p_reg(31);

#[inline]
const fn v_reg(p_reg: PReg) -> VReg {
    VReg::new(p_reg.index(), p_reg.class())
}

pub const V_ZERO: VReg = v_reg(P_ZERO);
pub const V_RA  : VReg = v_reg(P_RA  );
pub const V_SP  : VReg = v_reg(P_SP  );
pub const V_A0  : VReg = v_reg(P_A0  );
pub const V_A1  : VReg = v_reg(P_A1  );
pub const V_A2  : VReg = v_reg(P_A2  );
pub const V_A3  : VReg = v_reg(P_A3  );
pub const V_A4  : VReg = v_reg(P_A4  );
pub const V_A5  : VReg = v_reg(P_A5  );
pub const V_A6  : VReg = v_reg(P_A6  );
pub const V_A7  : VReg = v_reg(P_A7  );
pub const V_T0  : VReg = v_reg(P_T0  );
pub const V_T1  : VReg = v_reg(P_T1  );
pub const V_T2  : VReg = v_reg(P_T2  );
pub const V_T3  : VReg = v_reg(P_T3  );
pub const V_T4  : VReg = v_reg(P_T4  );
pub const V_T5  : VReg = v_reg(P_T5  );
pub const V_T6  : VReg = v_reg(P_T6  );
pub const V_T7  : VReg = v_reg(P_T7  );
pub const V_S0  : VReg = v_reg(P_S0  );
pub const V_S1  : VReg = v_reg(P_S1  );
pub const V_S2  : VReg = v_reg(P_S2  );
pub const V_S3  : VReg = v_reg(P_S3  );
pub const V_S4  : VReg = v_reg(P_S4  );
pub const V_S5  : VReg = v_reg(P_S5  );
pub const V_S6  : VReg = v_reg(P_S6  );
pub const V_S7  : VReg = v_reg(P_S7  );
pub const V_S8  : VReg = v_reg(P_S8  );
pub const V_S9  : VReg = v_reg(P_S9  );
pub const V_S10 : VReg = v_reg(P_S10 );
pub const V_S11 : VReg = v_reg(P_S11 );
pub const V_S12 : VReg = v_reg(P_S12 );

macro_rules! def_reg {
    ($name:ident, $w_name:ident, $v_reg:ident) => {
        #[inline]
        pub fn $name() -> Reg {
            Reg::from($v_reg)
        }

        #[inline]
        pub fn $w_name() -> Writable<Reg> {
            Writable::from_reg(Reg::from($v_reg))
        }
    };
}

def_reg!(zero, zero_w, V_ZERO);
def_reg!(ra  , ra_w  , V_RA  );
def_reg!(sp  , sp_w  , V_SP  );
def_reg!(a0  , a0_w  , V_A0  );
def_reg!(a1  , a1_w  , V_A1  );
def_reg!(a2  , a2_w  , V_A2  );
def_reg!(a3  , a3_w  , V_A3  );
def_reg!(a4  , a4_w  , V_A4  );
def_reg!(a5  , a5_w  , V_A5  );
def_reg!(a6  , a6_w  , V_A6  );
def_reg!(a7  , a7_w  , V_A7  );
def_reg!(t0  , t0_w  , V_T0  );
def_reg!(t1  , t1_w  , V_T1  );
def_reg!(t2  , t2_w  , V_T2  );
def_reg!(t3  , t3_w  , V_T3  );
def_reg!(t4  , t4_w  , V_T4  );
def_reg!(t5  , t5_w  , V_T5  );
def_reg!(t6  , t6_w  , V_T6  );
def_reg!(t7  , t7_w  , V_T7  );
def_reg!(s0  , s0_w  , V_S0  );
def_reg!(s1  , s1_w  , V_S1  );
def_reg!(s2  , s2_w  , V_S2  );
def_reg!(s3  , s3_w  , V_S3  );
def_reg!(s4  , s4_w  , V_S4  );
def_reg!(s5  , s5_w  , V_S5  );
def_reg!(s6  , s6_w  , V_S6  );
def_reg!(s7  , s7_w  , V_S7  );
def_reg!(s8  , s8_w  , V_S8  );
def_reg!(s9  , s9_w  , V_S9  );
def_reg!(s10 , s10_w , V_S10 );
def_reg!(s11 , s11_w , V_S11 );
def_reg!(s12 , s12_w , V_S12 );

pub fn create_reg_environment(_flags: &super::settings::Flags) -> MachineEnv {
    let preferred_regs_by_class = {
        // t7 not included because we use it as a temporary in certain pseudo-instructions
        let regs = vec![
            P_A0, P_A1, P_A2, P_A3, P_A4, P_A5, P_A6, P_A7,
            P_T0, P_T1, P_T2, P_T3, P_T4, P_T5, P_T6,
        ];
        [regs, vec![]]
    };

    let non_preferred_regs_by_class = {
        // s12 not included because we use it as the frame pointer
        let regs = vec![
            P_S0, P_S1, P_S2, P_S3, P_S4, P_S5, P_S6, P_S7,
            P_S8, P_S9, P_S10, P_S11,
        ];
        [regs, vec![]]
    };

    MachineEnv {
        preferred_regs_by_class,
        non_preferred_regs_by_class,
        fixed_stack_slots: vec![],
    }
}

#[inline]
pub(crate) fn real_reg_to_reg(x: RealReg) -> Reg {
    let v_reg = VReg::new(x.hw_enc() as usize, x.class());
    Reg::from(v_reg)
}
