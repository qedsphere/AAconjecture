import UnifiedAA.ScalarSimulation
import Mathlib.Data.Nat.Log

/-! Exact power-of-two rounding for bucket counts and independent repetition.
Using the natural ceiling logarithm avoids approximate real arithmetic. -/

namespace UnifiedAA

noncomputable def dyadicExponent (r : ℝ) : ℕ := Nat.clog 2 ⌈r⌉₊

noncomputable def dyadicCapacity (r : ℝ) : ℕ := 2 ^ dyadicExponent r

theorem le_dyadicCapacity (r : ℝ) : r ≤ (dyadicCapacity r : ℝ) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) ⌈r⌉₊
  exact (Nat.le_ceil r).trans (by exact_mod_cast h)

/-- Rounding a number greater than one up to a power of two loses less than
a factor of two, including when the number is already a power of two. -/
theorem dyadicCapacity_lt_twice (r : ℝ) (hr : 1 < r) :
    (dyadicCapacity r : ℝ) < 2 * r := by
  have hn : 1 < ⌈r⌉₊ := Nat.lt_ceil.mpr (by simpa using hr)
  have hk : 0 < dyadicExponent r := Nat.clog_pos (by decide) hn
  have hp : (2 : ℝ) ^ (dyadicExponent r).pred < r := by
    have h := Nat.lt_ceil.mp (Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicExponent] using h
  have heq : (dyadicCapacity r : ℝ) = (2 : ℝ) ^ (dyadicExponent r).pred * 2 := by
    simp only [dyadicCapacity, Nat.cast_pow, Nat.cast_ofNat]
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk]
    rw [pow_succ]
  rw [heq]
  linarith

noncomputable def bucketBits (t : ℝ) : ℕ := dyadicExponent (16 / t)

noncomputable def bucketCount (t : ℝ) : ℕ := 2 ^ bucketBits t

theorem bucketCount_spec (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    16 ≤ (bucketCount t : ℝ) * t ∧ (bucketCount t : ℝ) < 32 / t := by
  have hlo := (div_le_iff₀ ht).mp (le_dyadicCapacity (16 / t))
  have hr : (1 : ℝ) < 16 / t := (lt_div_iff₀ ht).mpr (by linarith)
  have hhi := dyadicCapacity_lt_twice (16 / t) hr
  constructor
  · exact hlo
  · change (dyadicCapacity (16 / t) : ℝ) < 32 / t
    convert hhi using 1 <;> ring

/-- With this many repetitions, a per-run failure probability at most one
half amplifies to at most eta. The eta=1 endpoint permits zero repetitions. -/
theorem dyadic_repetition_bound (η : ℝ) (hη : 0 < η) :
    (1 / 2 : ℝ) ^ dyadicExponent (1 / η) ≤ η := by
  rw [div_pow, one_pow]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ dyadicExponent (1 / η))).mpr
  have h := (div_le_iff₀ hη).mp (le_dyadicCapacity (1 / η))
  simpa only [dyadicCapacity, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using h

end UnifiedAA
