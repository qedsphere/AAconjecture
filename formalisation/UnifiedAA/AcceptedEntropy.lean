import UnifiedAA.FiniteProbability
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Accepted-output min-entropy for finite output distributions (Theorem 4.3,
manuscript p. 27). Invalid outputs have weight zero. A maximum over all outputs
therefore implements the manuscript's empty-valid-set convention, while its
positive-acceptance use always has a positive, attained valid maximum.

The logarithm is a total real function, but the entropy-to-heavy-output theorem
uses it only when acceptance is positive. The soundness contradiction and the
operational extractor are assembled separately. -/

namespace UnifiedAA

open scoped BigOperators

variable {Y : Type*} [Fintype Y]

/-- Unnormalized accepted weight; rejected outcomes have weight zero. -/
noncomputable def acceptedWeight (p : Y → ℝ) (valid : Y → Prop) (y : Y) : ℝ := by
  classical
  exact if valid y then p y else 0

/-- Acceptance probability when `p` is a normalized output law. -/
noncomputable def acceptedMass (p : Y → ℝ) (valid : Y → Prop) : ℝ :=
  ∑ y, acceptedWeight p valid y

theorem acceptedWeight_nonneg (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (y : Y) : 0 ≤ acceptedWeight p valid y := by
  classical
  by_cases hy : valid y <;> simp [acceptedWeight, hy, hp y]

theorem acceptedWeight_le (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (y : Y) : acceptedWeight p valid y ≤ p y := by
  classical
  by_cases hy : valid y <;> simp [acceptedWeight, hy, hp y]

theorem acceptedMass_nonneg (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) : 0 ≤ acceptedMass p valid :=
  Finset.sum_nonneg (fun y _ => acceptedWeight_nonneg p valid hp y)

theorem acceptedMass_le_one (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (total : ∑ y, p y = 1) : acceptedMass p valid ≤ 1 := by
  calc
    acceptedMass p valid ≤ ∑ y, p y :=
      Finset.sum_le_sum (fun y _ => acceptedWeight_le p valid hp y)
    _ = 1 := total

theorem acceptedWeight_le_mass (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (y : Y) : acceptedWeight p valid y ≤ acceptedMass p valid := by
  classical
  exact Finset.single_le_sum (fun z _ => acceptedWeight_nonneg p valid hp z)
    (Finset.mem_univ y)

/-- Conditioning on acceptance produces a normalized finite law. -/
noncomputable def acceptedLaw (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (hacc : 0 < acceptedMass p valid) : FiniteLaw Y where
  weight y := acceptedWeight p valid y / acceptedMass p valid
  nonneg y := div_nonneg (acceptedWeight_nonneg p valid hp y) hacc.le
  total := by
    rw [← Finset.sum_div]
    change acceptedMass p valid / acceptedMass p valid = 1
    exact div_self (ne_of_gt hacc)

theorem acceptedLaw_weight_of_valid (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (hacc : 0 < acceptedMass p valid)
    (y : Y) (hy : valid y) :
    (acceptedLaw p valid hp hacc).weight y = p y / acceptedMass p valid := by
  simp [acceptedLaw, acceptedWeight, hy]

variable [Nonempty Y]

/-- The largest unnormalized accepted weight, with value zero if no output is valid. -/
noncomputable def maxAcceptedMass (p : Y → ℝ) (valid : Y → Prop) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (acceptedWeight p valid)

theorem acceptedWeight_le_max (p : Y → ℝ) (valid : Y → Prop) (y : Y) :
    acceptedWeight p valid y ≤ maxAcceptedMass p valid := by
  classical
  exact Finset.le_sup' (acceptedWeight p valid) (Finset.mem_univ y)

theorem maxAcceptedMass_nonneg (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) : 0 ≤ maxAcceptedMass p valid := by
  let y : Y := Classical.choice inferInstance
  exact (acceptedWeight_nonneg p valid hp y).trans (acceptedWeight_le_max p valid y)

theorem maxAcceptedMass_le_mass (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) : maxAcceptedMass p valid ≤ acceptedMass p valid := by
  classical
  exact Finset.sup'_le Finset.univ_nonempty (acceptedWeight p valid)
    (fun y _ => acceptedWeight_le_mass p valid hp y)

theorem maxAcceptedMass_eq_zero_of_no_valid (p : Y → ℝ) (valid : Y → Prop)
    (hn : ∀ y, ¬ valid y) : maxAcceptedMass p valid = 0 := by
  classical
  exact Finset.sup'_eq_of_forall Finset.univ_nonempty (acceptedWeight p valid)
    (fun y _ => by simp [acceptedWeight, hn y])

theorem exists_eq_maxAcceptedMass (p : Y → ℝ) (valid : Y → Prop) :
    ∃ y, maxAcceptedMass p valid = acceptedWeight p valid y := by
  classical
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset Y))
    Finset.univ_nonempty (acceptedWeight p valid)
  exact ⟨y, hy⟩

theorem maxAcceptedMass_pos_of_mass_pos (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (hacc : 0 < acceptedMass p valid) :
    0 < maxAcceptedMass p valid := by
  by_contra hn
  have hm : maxAcceptedMass p valid ≤ 0 := le_of_not_gt hn
  have hz : ∀ y, acceptedWeight p valid y = 0 := fun y =>
    le_antisymm ((acceptedWeight_le_max p valid y).trans hm)
      (acceptedWeight_nonneg p valid hp y)
  have hzero : acceptedMass p valid = 0 := by simp [acceptedMass, hz]
  linarith

/-- A positive maximum must be achieved at a valid output, not at one of the
zeroed rejected outputs. -/
theorem exists_valid_eq_maxAcceptedMass (p : Y → ℝ) (valid : Y → Prop)
    (hm : 0 < maxAcceptedMass p valid) :
    ∃ y, valid y ∧ maxAcceptedMass p valid = p y := by
  classical
  obtain ⟨y, hy⟩ := exists_eq_maxAcceptedMass p valid
  have hwy : 0 < acceptedWeight p valid y := by simpa only [hy] using hm
  have hv : valid y := by
    by_contra hn
    simp [acceptedWeight, hn] at hwy
  exact ⟨y, hv, by simpa [acceptedWeight, hv] using hy⟩

/-- Accepted-output min-entropy, interpreted only when acceptance is positive. -/
noncomputable def acceptedMinEntropy (p : Y → ℝ) (valid : Y → Prop) : ℝ :=
  -Real.logb 2 (maxAcceptedMass p valid / acceptedMass p valid)

/-- Low accepted-output min-entropy produces an unconditionally heavy valid
output. The witness depends on the output law, independently of any hash seed. -/
theorem exists_heavy_of_accepted_entropy_le (p : Y → ℝ) (valid : Y → Prop)
    (hp : ∀ y, 0 ≤ p y) (a0 h : ℝ) (ha0 : 0 < a0)
    (haccept : a0 ≤ acceptedMass p valid) (hentropy : acceptedMinEntropy p valid ≤ h) :
    ∃ y, valid y ∧ a0 * (2 : ℝ) ^ (-h) ≤ p y := by
  have ha : 0 < acceptedMass p valid := lt_of_lt_of_le ha0 haccept
  have hm : 0 < maxAcceptedMass p valid := maxAcceptedMass_pos_of_mass_pos p valid hp ha
  obtain ⟨y, hvalid, hmax⟩ := exists_valid_eq_maxAcceptedMass p valid hm
  have hlog : -h ≤ Real.logb 2 (maxAcceptedMass p valid / acceptedMass p valid) := by
    unfold acceptedMinEntropy at hentropy
    linarith
  have hpow : (2 : ℝ) ^ (-h) ≤ maxAcceptedMass p valid / acceptedMass p valid :=
    (Real.le_logb_iff_rpow_le (by norm_num) (div_pos hm ha)).mp hlog
  have hmass : acceptedMass p valid * (2 : ℝ) ^ (-h) ≤ maxAcceptedMass p valid := by
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hpow
  refine ⟨y, hvalid, ?_⟩
  calc
    a0 * (2 : ℝ) ^ (-h) ≤ acceptedMass p valid * (2 : ℝ) ^ (-h) :=
      mul_le_mul_of_nonneg_right haccept (Real.rpow_pos_of_pos (by norm_num) _).le
    _ ≤ maxAcceptedMass p valid := hmass
    _ = p y := hmax

/-- The threshold used in Theorem 4.3 meets the extractor's positivity and
unit-interval conditions. The manuscript's additional bound `h ≤ L` is not
needed for this arithmetic fact or the preceding heavy-output implication. -/
theorem accepted_entropy_threshold_bounds (a0 h : ℝ)
    (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (hh : 0 ≤ h) :
    0 < a0 * (2 : ℝ) ^ (-h) ∧ a0 * (2 : ℝ) ^ (-h) ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ (-h) := Real.rpow_pos_of_pos (by norm_num) _
  have hp1 : (2 : ℝ) ^ (-h) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hh)
  exact ⟨mul_pos ha0 hp, by simpa using mul_le_mul ha01 hp1 hp.le (by norm_num : (0 : ℝ) ≤ 1)⟩

end UnifiedAA
