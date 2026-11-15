import UnifiedAA.WalshConvolution

/-! A Walsh expansion of coefficient norm at most one is the mean of a
finite random signed-parity or constant map. Constants consume no input
coordinates. Conditioning on a specified output also has an explicit
support-cost bound. This file does not model the number of rejection proposals. -/

namespace UnifiedAA

namespace FiniteLaw
variable {A : Type*} [Fintype A]

/-- Exact finite conditioning on a positive-probability event. -/
noncomputable def conditionOn (μ : FiniteLaw A) (P : A → Prop)
    (hP : 0 < μ.prob P) : FiniteLaw A := by
  classical
  exact {
    weight := fun a => (if P a then μ.weight a else 0) / μ.prob P
    nonneg := fun a => div_nonneg
      (by split_ifs <;> simp [μ.nonneg]) hP.le
    total := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      change μ.prob P / μ.prob P = 1
      exact div_self (ne_of_gt hP) }

theorem expect_conditionOn (μ : FiniteLaw A) (P : A → Prop)
    (hP : 0 < μ.prob P) (f : A → ℝ) :
    (μ.conditionOn P hP).expect f =
      μ.expect (fun a => if P a then f a else 0) / μ.prob P := by
  classical
  unfold expect conditionOn
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [h] <;> ring

/-- For a nonnegative cost, conditioning increases its expectation by at
most the reciprocal of the conditioning probability. -/
theorem expect_conditionOn_le (μ : FiniteLaw A) (P : A → Prop)
    (hP : 0 < μ.prob P) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (μ.conditionOn P hP).expect f ≤ μ.expect f / μ.prob P := by
  classical
  rw [expect_conditionOn]
  apply (div_le_div_iff_of_pos_right hP).mpr
  apply μ.expect_mono
  intro a
  by_cases h : P a <;> simp [h, hf a]

end FiniteLaw

namespace ParityUpdate
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The first summand contains two constant maps. The second contains one
signed parity for each support, with its sign determined by the coefficient. -/
abbrev Seed (I : Type*) := Bool ⊕ Finset I

noncomputable def coefficientSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

theorem abs_mul_coefficientSign (r : ℝ) : |r| * coefficientSign r = r := by
  by_cases h : 0 ≤ r
  · simp [coefficientSign, h, abs_of_nonneg h]
  · simp [coefficientSign, h, abs_of_neg (lt_of_not_ge h)]

theorem coefficientSign_sq (r : ℝ) : coefficientSign r ^ 2 = 1 := by
  unfold coefficientSign
  split_ifs <;> norm_num

noncomputable def weight (c : Finset I → ℝ) : Seed I → ℝ
  | .inl _ => (1 - WalshConvolution.l1Norm c) / 2
  | .inr S => |c S|

theorem weight_nonneg (c : Finset I → ℝ) (hc : WalshConvolution.l1Norm c ≤ 1)
    (s : Seed I) : 0 ≤ weight c s := by
  cases s with
  | inl b => exact div_nonneg (sub_nonneg.mpr hc) (by norm_num)
  | inr S => exact abs_nonneg _

theorem weight_total (c : Finset I → ℝ) : ∑ s, weight c s = 1 := by
  simp only [Fintype.sum_sum_type, weight, Fintype.sum_bool]
  change (1 - WalshConvolution.l1Norm c) / 2 +
    (1 - WalshConvolution.l1Norm c) / 2 + WalshConvolution.l1Norm c = 1
  ring

/-- Both signs of the unused mass are added as constants, so their means
cancel. Empty-support Fourier mass is also a constant and has zero cost. -/
noncomputable def law (c : Finset I → ℝ) (hc : WalshConvolution.l1Norm c ≤ 1) :
    FiniteLaw (Seed I) where
  weight := weight c
  nonneg := weight_nonneg c hc
  total := weight_total c

def support : Seed I → Finset I
  | .inl _ => ∅
  | .inr S => S

noncomputable def value (c : Finset I → ℝ) : Seed I → (I → Bool) → ℝ
  | .inl b, _ => if b then 1 else -1
  | .inr S, x => coefficientSign (c S) * walsh S x

theorem value_sq (c : Finset I → ℝ) (s : Seed I) (x : I → Bool) :
    value c s x ^ 2 = 1 := by
  cases s with
  | inl b => cases b <;> norm_num [value]
  | inr S =>
      have hw : walsh S x ^ 2 = 1 := by
        rw [pow_two, walsh_mul]
        simp [walsh_empty]
      simp only [value, mul_pow, coefficientSign_sq, hw, one_mul]

theorem value_eq_one_or_neg_one (c : Finset I → ℝ) (s : Seed I) (x : I → Bool) :
    value c s x = 1 ∨ value c s x = -1 :=
  sq_eq_one_iff.mp (value_sq c s x)

/-- The random map has precisely the prescribed conditional mean. -/
theorem expect_value (c : Finset I → ℝ) (hc : WalshConvolution.l1Norm c ≤ 1)
    (x : I → Bool) :
    (law c hc).expect (fun s => value c s x) = WalshConvolution.eval c x := by
  change (∑ s, weight c s * value c s x) = ∑ S, c S * walsh S x
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, weight, value,
    ↓reduceIte, mul_one, mul_neg_one, add_neg_cancel, zero_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [← mul_assoc, abs_mul_coefficientSign]

/-- The expected number of requested coordinates is the weighted coefficient
norm, with no contribution from either kind of constant map. -/
theorem expect_support_card (c : Finset I → ℝ) (hc : WalshConvolution.l1Norm c ≤ 1) :
    (law c hc).expect (fun s => ((support s).card : ℝ)) =
      WalshConvolution.degreeNorm c := by
  change (∑ s, weight c s * ((support s).card : ℝ)) =
    ∑ S, (S.card : ℝ) * |c S|
  simp only [Fintype.sum_sum_type, support, weight, Finset.card_empty,
    Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro S _
  exact mul_comm _ _

/-- The resulting spin is the Bernoulli law determined by its mean. -/
theorem prob_value_one (c : Finset I → ℝ) (hc : WalshConvolution.l1Norm c ≤ 1)
    (x : I → Bool) :
    (law c hc).prob (fun s => value c s x = 1) =
      (1 + WalshConvolution.eval c x) / 2 := by
  classical
  have hpoint (s : Seed I) :
      (if value c s x = 1 then (law c hc).weight s else 0) =
        (law c hc).weight s * ((1 / 2 : ℝ) * (1 + value c s x)) := by
    rcases value_eq_one_or_neg_one c s x with h | h
    · rw [h]
      simp
    · rw [h]
      norm_num
  calc
    _ = (law c hc).expect (fun s => (1 / 2 : ℝ) * (1 + value c s x)) :=
      Finset.sum_congr rfl (fun s _ => hpoint s)
    _ = (1 + WalshConvolution.eval c x) / 2 := by
      rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_add, FiniteLaw.expect_const,
        expect_value]
      ring

theorem prob_value_neg_one (c : Finset I → ℝ) (hc : WalshConvolution.l1Norm c ≤ 1)
    (x : I → Bool) :
    (law c hc).prob (fun s => value c s x = -1) =
      (1 - WalshConvolution.eval c x) / 2 := by
  have heq : (fun s => value c s x = -1) = (fun s => ¬ value c s x = 1) := by
    funext s
    apply propext
    rcases value_eq_one_or_neg_one c s x with h | h <;> simp [h]
  rw [heq, FiniteLaw.prob_not, prob_value_one]
  ring

/-- A positive-probability observed spin yields an exact posterior random
map with conditional expected support bounded by W(c)/p(spin). -/
theorem posterior_support_cost_le (c : Finset I → ℝ)
    (hc : WalshConvolution.l1Norm c ≤ 1) (x : I → Bool) (y : ℝ)
    (hy : 0 < (law c hc).prob (fun s => value c s x = y)) :
    ((law c hc).conditionOn (fun s => value c s x = y) hy).expect
        (fun s => ((support s).card : ℝ)) ≤
      WalshConvolution.degreeNorm c /
        (law c hc).prob (fun s => value c s x = y) := by
  have h := (law c hc).expect_conditionOn_le (fun s => value c s x = y) hy
    (fun s => ((support s).card : ℝ)) (fun s => Nat.cast_nonneg _)
  rwa [expect_support_card] at h

end ParityUpdate
end UnifiedAA
