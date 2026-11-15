import UnifiedAA.FourierPotential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite convolution of Walsh coefficients, with its coefficient ℓ¹ norm
and weighted degree seminorm. These are coefficient norms: multiplication
uses symmetric difference of Fourier supports, rather than pointwise
multiplication of coefficient functions. No analytic convergence assumption
is needed for the estimates in this file. -/

namespace UnifiedAA.WalshConvolution

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def eval (c : Finset I → ℝ) (x : I → Bool) : ℝ :=
  ∑ S, c S * walsh S x

/-- The coefficient of `U` in the product of two Walsh expansions. -/
noncomputable def convolve (c d : Finset I → ℝ) (U : Finset I) : ℝ :=
  ∑ S, ∑ T, if symmDiff S T = U then c S * d T else 0

/-- The coefficient ℓ¹ norm, including the constant coefficient. -/
noncomputable def l1Norm (c : Finset I → ℝ) : ℝ := ∑ S, |c S|

/-- The weighted degree seminorm. The constant coefficient has weight zero. -/
noncomputable def degreeNorm (c : Finset I → ℝ) : ℝ :=
  ∑ S, (S.card : ℝ) * |c S|

def unit (S : Finset I) : ℝ := if S = ∅ then 1 else 0

theorem sum_convolve_mul (c d f : Finset I → ℝ) :
    (∑ U, convolve c d U * f U) =
      ∑ S, ∑ T, (c S * d T) * f (symmDiff S T) := by
  classical
  simp only [convolve, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

theorem eval_convolve (c d : Finset I → ℝ) (x : I → Bool) :
    eval (convolve c d) x = eval c x * eval d x := by
  change (∑ U, convolve c d U * walsh U x) =
    (∑ S, c S * walsh S x) * (∑ T, d T * walsh T x)
  rw [sum_convolve_mul, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [← walsh_mul]
  ring

/-- Orthogonality recovers each coefficient from its evaluated function. -/
theorem expect_eval_mul_walsh (c : Finset I → ℝ) (S : Finset I) :
    (FiniteLaw.uniform (I → Bool)).expect (fun x => eval c x * walsh S x) = c S := by
  have h : (fun x => eval c x * walsh S x) =
      fun x => ∑ T, c T * (walsh T x * walsh S x) := by
    funext x
    simp only [eval, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [h, FiniteLaw.expect_sum]
  simp only [FiniteLaw.expect_const_mul, uniform_expect_walsh_mul]
  simp [mul_ite]

theorem eval_injective : Function.Injective (eval (I := I)) := by
  intro c d h
  funext S
  rw [← expect_eval_mul_walsh c S, ← expect_eval_mul_walsh d S, h]

@[simp] theorem eval_unit (x : I → Bool) : eval (unit (I := I)) x = 1 := by
  simp [eval, unit, ite_mul, walsh_empty]

theorem convolve_comm (c d : Finset I → ℝ) : convolve c d = convolve d c := by
  apply eval_injective
  funext x
  simp only [eval_convolve, mul_comm]

theorem convolve_assoc (a b c : Finset I → ℝ) :
    convolve (convolve a b) c = convolve a (convolve b c) := by
  apply eval_injective
  funext x
  simp only [eval_convolve, mul_assoc]

@[simp] theorem unit_convolve (c : Finset I → ℝ) : convolve unit c = c := by
  apply eval_injective
  funext x
  simp only [eval_convolve, eval_unit, one_mul]

@[simp] theorem convolve_unit (c : Finset I → ℝ) : convolve c unit = c := by
  rw [convolve_comm, unit_convolve]

theorem l1Norm_nonneg (c : Finset I → ℝ) : 0 ≤ l1Norm c :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem degreeNorm_nonneg (c : Finset I → ℝ) : 0 ≤ degreeNorm c :=
  Finset.sum_nonneg (fun S _ => mul_nonneg (Nat.cast_nonneg S.card) (abs_nonneg _))

@[simp] theorem l1Norm_zero : l1Norm (0 : Finset I → ℝ) = 0 := by
  simp [l1Norm]

@[simp] theorem degreeNorm_zero : degreeNorm (0 : Finset I → ℝ) = 0 := by
  simp [degreeNorm]

theorem abs_coefficient_le_l1Norm (c : Finset I → ℝ) (S : Finset I) :
    |c S| ≤ l1Norm c :=
  Finset.single_le_sum (fun T _ => abs_nonneg (c T)) (Finset.mem_univ S)

@[simp] theorem l1Norm_eq_zero_iff (c : Finset I → ℝ) : l1Norm c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext S
    change c S = 0
    exact abs_eq_zero.mp (le_antisymm
      ((abs_coefficient_le_l1Norm c S).trans_eq h) (abs_nonneg _))
  · intro h
    rw [h, l1Norm_zero]

/-- Evaluation is controlled by the coefficient norm. -/
theorem abs_eval_le_l1Norm (c : Finset I → ℝ) (x : I → Bool) :
    |eval c x| ≤ l1Norm c := by
  have hw (S : Finset I) : |walsh S x| = 1 := by
    unfold walsh
    rw [Finset.abs_prod]
    apply Finset.prod_eq_one
    intro i _
    cases x i <;> norm_num
  calc
    _ ≤ ∑ S, |c S * walsh S x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, hw, mul_one, l1Norm]

/-- This finite-dimensional bound also gives continuity of the degree
seminorm with respect to the coefficient ℓ¹ norm. -/
theorem degreeNorm_le_card_mul_l1Norm (c : Finset I → ℝ) :
    degreeNorm c ≤ (Fintype.card I : ℝ) * l1Norm c := by
  simp only [degreeNorm, l1Norm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact_mod_cast Finset.card_le_univ S

@[simp] theorem l1Norm_unit : l1Norm (unit (I := I)) = 1 := by
  simp [l1Norm, unit, abs_ite]

@[simp] theorem degreeNorm_unit : degreeNorm (unit (I := I)) = 0 := by
  simp [degreeNorm, unit, abs_ite, mul_ite]

theorem l1Norm_add_le (c d : Finset I → ℝ) :
    l1Norm (c + d) ≤ l1Norm c + l1Norm d := by
  simp only [l1Norm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun S _ => abs_add (c S) (d S))

theorem degreeNorm_add_le (c d : Finset I → ℝ) :
    degreeNorm (c + d) ≤ degreeNorm c + degreeNorm d := by
  simp only [degreeNorm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_add (c S) (d S)) (Nat.cast_nonneg _)

theorem l1Norm_smul (r : ℝ) (c : Finset I → ℝ) :
    l1Norm (r • c) = |r| * l1Norm c := by
  simp only [l1Norm, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem degreeNorm_smul (r : ℝ) (c : Finset I → ℝ) :
    degreeNorm (r • c) = |r| * degreeNorm c := by
  simp only [degreeNorm, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem abs_convolve_le (c d : Finset I → ℝ) (U : Finset I) :
    |convolve c d U| ≤ convolve (fun S => |c S|) (fun T => |d T|) U := by
  unfold convolve
  calc
    _ ≤ ∑ S, |∑ T, if symmDiff S T = U then c S * d T else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S, ∑ T, |if symmDiff S T = U then c S * d T else 0| :=
      Finset.sum_le_sum (fun S _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      by_cases h : symmDiff S T = U <;> simp [h, abs_mul]

/-- A nonnegative weight can be summed before merging equal supports. -/
theorem weighted_abs_convolve_le (c d w : Finset I → ℝ) (hw : ∀ U, 0 ≤ w U) :
    (∑ U, w U * |convolve c d U|) ≤
      ∑ S, ∑ T, w (symmDiff S T) * (|c S| * |d T|) := by
  calc
    _ ≤ ∑ U, w U * convolve (fun S => |c S|) (fun T => |d T|) U :=
      Finset.sum_le_sum (fun U _ =>
        mul_le_mul_of_nonneg_left (abs_convolve_le c d U) (hw U))
    _ = ∑ U, convolve (fun S => |c S|) (fun T => |d T|) U * w U := by
      apply Finset.sum_congr rfl
      intro U _
      exact mul_comm _ _
    _ = ∑ S, ∑ T, (|c S| * |d T|) * w (symmDiff S T) :=
      sum_convolve_mul _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      exact mul_comm _ _

/-- The coefficient ℓ¹ norm is submultiplicative for Walsh convolution. -/
theorem l1Norm_convolve_le (c d : Finset I → ℝ) :
    l1Norm (convolve c d) ≤ l1Norm c * l1Norm d := by
  have h := weighted_abs_convolve_le c d (fun _ => 1) (fun _ => zero_le_one)
  simpa only [one_mul, l1Norm, Finset.sum_mul_sum] using h

private theorem card_symmDiff_le (S T : Finset I) :
    ((symmDiff S T).card : ℝ) ≤ (S.card : ℝ) + (T.card : ℝ) := by
  have h : (symmDiff S T).card ≤ S.card + T.card :=
    (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le S T)
  exact_mod_cast h

/-- The degree weight is subadditive under symmetric difference. This yields
a Leibniz inequality, although the degree operator is not a derivation. -/
theorem degreeNorm_convolve_le (c d : Finset I → ℝ) :
    degreeNorm (convolve c d) ≤
      degreeNorm c * l1Norm d + l1Norm c * degreeNorm d := by
  calc
    _ ≤ ∑ S, ∑ T, ((symmDiff S T).card : ℝ) * (|c S| * |d T|) :=
      weighted_abs_convolve_le c d (fun U => (U.card : ℝ)) (fun U => Nat.cast_nonneg _)
    _ ≤ ∑ S, ∑ T, ((S.card : ℝ) + (T.card : ℝ)) * (|c S| * |d T|) := by
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_right (card_symmDiff_le S T)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [degreeNorm, l1Norm, Finset.sum_mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      ring

/-- Powers for convolution, without replacing the pointwise multiplication
instance on coefficient functions. -/
noncomputable def power (c : Finset I → ℝ) : ℕ → Finset I → ℝ
  | 0 => unit
  | n + 1 => convolve (power c n) c

@[simp] theorem power_zero (c : Finset I → ℝ) : power c 0 = unit := rfl

theorem power_succ (c : Finset I → ℝ) (n : ℕ) :
    power c (n + 1) = convolve (power c n) c := rfl

@[simp] theorem power_one (c : Finset I → ℝ) : power c 1 = c := by
  simp [power]

theorem eval_power (c : Finset I → ℝ) (n : ℕ) (x : I → Bool) :
    eval (power c n) x = eval c x ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp only [power_succ, eval_convolve, ih, pow_succ]

theorem l1Norm_power_le (c : Finset I → ℝ) (n : ℕ) :
    l1Norm (power c n) ≤ l1Norm c ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    rw [power_succ, pow_succ]
    exact (l1Norm_convolve_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (l1Norm_nonneg c))

theorem degreeNorm_power_succ_le (c : Finset I → ℝ) (n : ℕ) :
    degreeNorm (power c (n + 1)) ≤
      ((n + 1 : ℕ) : ℝ) * l1Norm c ^ n * degreeNorm c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [power_succ c (n + 1)]
    calc
      _ ≤ degreeNorm (power c (n + 1)) * l1Norm c +
          l1Norm (power c (n + 1)) * degreeNorm c := degreeNorm_convolve_le _ _
      _ ≤ (((n + 1 : ℕ) : ℝ) * l1Norm c ^ n * degreeNorm c) * l1Norm c +
          l1Norm c ^ (n + 1) * degreeNorm c :=
        add_le_add (mul_le_mul_of_nonneg_right ih (l1Norm_nonneg c))
          (mul_le_mul_of_nonneg_right (l1Norm_power_le c (n + 1)) (degreeNorm_nonneg c))
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_succ, Nat.cast_one, pow_succ]
        ring

theorem degreeNorm_power_le (c : Finset I → ℝ) (n : ℕ) :
    degreeNorm (power c n) ≤ (n : ℝ) * l1Norm c ^ (n - 1) * degreeNorm c := by
  cases n with
  | zero => simp
  | succ n => simpa using degreeNorm_power_succ_le c n

end UnifiedAA.WalshConvolution
