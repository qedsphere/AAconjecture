import UnifiedAA.DyadicRounding
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The natural power-of-two rounding used operationally is exactly the
manuscript's real ceiling logarithm on positive arguments. -/

namespace UnifiedAA

theorem dyadicExponent_eq_ceil_logb (r : ℝ) (hr : 0 < r) :
    dyadicExponent r = ⌈Real.logb 2 r⌉₊ := by
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    apply Nat.ceil_le.mpr
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hr).mp
      (Nat.le_ceil (Real.logb 2 r))
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using h
  · apply Nat.ceil_le.mpr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hr).mpr
    simpa only [dyadicCapacity, Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
      using le_dyadicCapacity r

end UnifiedAA
