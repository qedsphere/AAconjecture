import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Deterministic reconstruction in Theorem 4.1 (PDF p. 26)

All sums below are exact real sums over a finite output space. The hash and
the estimates are fixed. No oracle queries, distributions on hashes, or AA
simulation theorem are assumed or constructed in this module.
-/

namespace UnifiedAA

open scoped BigOperators

variable {Y B J : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq B]

/-- Total output mass in one hash bucket. -/
def bucketMass (p : Y → ℝ) (g : Y → B) (b : B) : ℝ :=
  ∑ y, if g y = b then p y else 0

/-- Bucket mass whose indicated output bit is one. -/
def bitMass (p : Y → ℝ) (g : Y → B) (bit : Y → J → Bool) (b : B) (j : J) : ℝ :=
  ∑ y, if g y = b ∧ bit y j = true then p y else 0

/-- All mass other than the designated output in its bucket. -/
def contamination (p : Y → ℝ) (g : Y → B) (yStar : Y) : ℝ :=
  ∑ y, if y ≠ yStar ∧ g y = g yStar then p y else 0

theorem contamination_nonneg (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (g : Y → B) (yStar : Y) : 0 ≤ contamination p g yStar := by
  unfold contamination
  exact Finset.sum_nonneg fun y _ => by split_ifs <;> simp_all

theorem bucketMass_eq (p : Y → ℝ) (g : Y → B) (yStar : Y) :
    bucketMass p g (g yStar) = p yStar + contamination p g yStar := by
  classical
  have h : ∀ y, (if g y = g yStar then p y else 0) =
      (if y = yStar then p yStar else 0) +
        (if y ≠ yStar ∧ g y = g yStar then p y else 0) := by
    intro y
    by_cases hy : y = yStar
    · subst y; simp
    · by_cases hg : g y = g yStar <;> simp [hy, hg]
  simp only [bucketMass, contamination, h, Finset.sum_add_distrib]
  simp

omit [DecidableEq Y] in
theorem bitMass_lower_of_true (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (g : Y → B) (bit : Y → J → Bool) (yStar : Y) (j : J)
    (hbit : bit yStar j = true) :
    p yStar ≤ bitMass p g bit (g yStar) j := by
  classical
  calc
    p yStar = (if g yStar = g yStar ∧ bit yStar j = true then p yStar else 0) := by
      simp [hbit]
    _ ≤ ∑ y, if g y = g yStar ∧ bit y j = true then p y else 0 := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun y => if g y = g yStar ∧ bit y j = true then p y else 0)
      · intro y _; split_ifs <;> simp_all
      · exact Finset.mem_univ _

theorem bitMass_upper_of_false (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (g : Y → B) (bit : Y → J → Bool) (yStar : Y) (j : J)
    (hbit : bit yStar j = false) :
    bitMass p g bit (g yStar) j ≤ contamination p g yStar := by
  classical
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : y = yStar
  · subst y; simp [hbit]
  · by_cases hg : g y = g yStar
    · by_cases hb : bit y j = true <;> simp [hy, hg, hb, hp y]
    · simp [hg]

/-- The actual threshold decoder used in the paper; ties decode to zero. -/
noncomputable def decodeBit (wHat uHat : ℝ) : Bool :=
  decide (wHat / 2 < uHat)

/-- An isolated t-heavy output is reconstructed at every bit. Estimates may
be negative or exceed one; only their additive errors are used. -/
theorem decodeBit_correct (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (g : Y → B) (bit : Y → J → Bool) (yStar : Y) (j : J)
    (t wHat uHat : ℝ) (ht : 0 < t) (heavy : t ≤ p yStar)
    (isolated : contamination p g yStar ≤ t / 4)
    (hw : |wHat - bucketMass p g (g yStar)| ≤ t / 16)
    (hu : |uHat - bitMass p g bit (g yStar) j| ≤ t / 16) :
    decodeBit wHat uHat = bit yStar j := by
  have hw' := abs_le.mp hw
  have hu' := abs_le.mp hu
  have hmass := bucketMass_eq p g yStar
  cases hb : bit yStar j with
  | false =>
      have hupper := bitMass_upper_of_false p hp g bit yStar j hb
      have : ¬ wHat / 2 < uHat := by linarith
      simp [decodeBit, this]
  | true =>
      have hlower := bitMass_lower_of_true p hp g bit yStar j hb
      have : wHat / 2 < uHat := by linarith
      simp [decodeBit, this]

/-- In particular, all coordinates of a bitstring are recovered exactly. -/
theorem decodeString_correct {L : ℕ}
    (p : (Fin L → Bool) → ℝ) (hp : ∀ y, 0 ≤ p y)
    (g : (Fin L → Bool) → B) (yStar : Fin L → Bool)
    (t wHat : ℝ) (uHat : Fin L → ℝ) (ht : 0 < t) (heavy : t ≤ p yStar)
    (isolated : contamination p g yStar ≤ t / 4)
    (hw : |wHat - bucketMass p g (g yStar)| ≤ t / 16)
    (hu : ∀ j, |uHat j - bitMass p g (fun y j => y j) (g yStar) j| ≤ t / 16) :
    (fun j => decodeBit wHat (uHat j)) = yStar := by
  funext j
  exact decodeBit_correct p hp g (fun y j => y j) yStar j t wHat (uHat j)
    ht heavy isolated hw (hu j)

omit [Fintype Y] [DecidableEq Y] in
/-- The pigeonhole step in Corollary 4.2, with explicit positivity of k. -/
theorem exists_heavy_of_sparse_mass (p : Y → ℝ)
    (S : Finset Y) (k : ℕ) (hk : 0 < k) (alpha : ℝ) (ha : 0 < alpha)
    (hcard : S.card ≤ k) (hmass : alpha ≤ ∑ y ∈ S, p y) :
    ∃ y ∈ S, alpha / k ≤ p y := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hne : S.Nonempty := by
    by_contra hn
    have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [this] at hmass
    linarith
  by_contra hn
  push Not at hn
  have hsum : ∑ y ∈ S, p y < ∑ _y ∈ S, alpha / k :=
    Finset.sum_lt_sum_of_nonempty hne fun y hy => hn y hy
  have hc : (S.card : ℝ) ≤ k := by exact_mod_cast hcard
  have hnonneg : 0 ≤ alpha / (k : ℝ) := le_of_lt (div_pos ha hk')
  have hbound : (S.card : ℝ) * (alpha / k) ≤ alpha := by
    calc
      _ ≤ (k : ℝ) * (alpha / k) := mul_le_mul_of_nonneg_right hc hnonneg
      _ = alpha := by field_simp
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

end UnifiedAA
