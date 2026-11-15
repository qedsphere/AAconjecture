import UnifiedAA.FourierPotential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Pinning Fourier interactions merges residual terms by signed sums.
The weighted interaction load cannot increase, even for arbitrary arity. -/

namespace UnifiedAA
variable {I : Type*} [Fintype I] [DecidableEq I]

def pinBits (P : Finset I) (a x : I → Bool) : I → Bool :=
  fun i => if i ∈ P then a i else x i

theorem abs_walsh_eq_one (S : Finset I) (x : I → Bool) : |walsh S x| = 1 := by
  unfold walsh
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> norm_num

theorem walsh_pinBits (S P : Finset I) (a x : I → Bool) :
    walsh S (pinBits P a x) = walsh (S ∩ P) a * walsh (S \ P) x := by
  have hu (T : Finset I) (y : I → Bool) : walsh T y =
      ∏ i, if i ∈ T then (if y i then (-1 : ℝ) else 1) else 1 :=
    (Fintype.prod_ite_mem T _).symm
  rw [hu, hu, hu, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hP : i ∈ P <;>
    cases a i <;> cases x i <;> simp [pinBits, hS, hP]

noncomputable def pinCoefficients (J : Finset I → ℝ) (P : Finset I)
    (a : I → Bool) (B : Finset I) : ℝ :=
  ∑ S, if S \ P = B then J S * walsh (S ∩ P) a else 0

/-- The merged coefficients represent exactly the pinned Hamiltonian,
including constant and singleton terms. -/
theorem pinCoefficients_eval (J : Finset I → ℝ) (P : Finset I) (a x : I → Bool) :
    (∑ B, pinCoefficients J P a B * walsh B x) =
      ∑ S, J S * walsh S (pinBits P a x) := by
  classical
  simp only [pinCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, walsh_pinBits]
  ring

theorem abs_pinCoefficients_le (J : Finset I → ℝ) (P : Finset I)
    (a : I → Bool) (B : Finset I) :
    |pinCoefficients J P a B| ≤ ∑ S, if S \ P = B then |J S| else 0 := by
  classical
  unfold pinCoefficients
  calc
    _ ≤ ∑ S, |if S \ P = B then J S * walsh (S ∩ P) a else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : S \ P = B <;> simp [h, abs_mul, abs_walsh_eq_one]

def interactionWeight (i : I) (S : Finset I) : ℝ :=
  if i ∈ S then ((S.card - 1 : ℕ) : ℝ) else 0

theorem interactionWeight_nonneg (i : I) (S : Finset I) : 0 ≤ interactionWeight i S := by
  unfold interactionWeight
  split_ifs <;> positivity

theorem interactionWeight_sdiff_le (i : I) (S P : Finset I) :
    interactionWeight i (S \ P) ≤ interactionWeight i S := by
  by_cases h : i ∈ S \ P
  · have hi : i ∈ S := (Finset.mem_sdiff.mp h).1
    simp only [interactionWeight, if_pos h, if_pos hi]
    exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_card Finset.sdiff_subset) 1
  · simp only [interactionWeight, if_neg h]
    exact interactionWeight_nonneg i S

noncomputable def weightedInteractionLoad (J : Finset I → ℝ) (i : I) : ℝ :=
  ∑ S, interactionWeight i S * |J S|

/-- Pinning and merging signed interactions never increases the weighted
load at any coordinate. Multiplication by beta≥0 preserves this bound. -/
theorem weightedInteractionLoad_pin_le (J : Finset I → ℝ) (P : Finset I)
    (a : I → Bool) (i : I) :
    weightedInteractionLoad (pinCoefficients J P a) i ≤ weightedInteractionLoad J i := by
  classical
  unfold weightedInteractionLoad
  calc
    _ ≤ ∑ B, interactionWeight i B * (∑ S, if S \ P = B then |J S| else 0) :=
      Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left
        (abs_pinCoefficients_le J P a B) (interactionWeight_nonneg i B))
    _ = ∑ S, interactionWeight i (S \ P) * |J S| := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      simp
    _ ≤ _ := Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_right
      (interactionWeight_sdiff_le i S P) (abs_nonneg _))

end UnifiedAA
