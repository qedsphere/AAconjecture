import UnifiedAA.FiniteProbability

/-!
Finite probability bounds used by the scalar estimator and the tablewise
amplification argument. The sample spaces and weights are arbitrary finite laws.
-/

namespace UnifiedAA.FiniteLaw

variable {A : Type*} [Fintype A]

/-- Mean squared error around the true mean. -/
def variance (μ : FiniteLaw A) (f : A → ℝ) : ℝ :=
  μ.expect (fun a => (f a - μ.expect f) ^ 2)

theorem variance_nonneg (μ : FiniteLaw A) (f : A → ℝ) :
    0 ≤ μ.variance f := by
  unfold variance
  calc
    0 = μ.expect (fun _ => (0 : ℝ)) := (μ.expect_const 0).symm
    _ ≤ μ.expect (fun a => (f a - μ.expect f) ^ 2) :=
      μ.expect_mono (fun a => sq_nonneg _)

/-- Centering at the exact mean makes the first moment vanish. -/
theorem expect_sub_mean (μ : FiniteLaw A) (f : A → ℝ) :
    μ.expect (fun a => f a - μ.expect f) = 0 := by
  unfold expect
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.total, one_mul]
  ring

/-- Exact variance decomposition: the conditional mean minimizes squared error
over constant answers. -/
theorem mse_eq_variance_add_sq (μ : FiniteLaw A) (f : A → ℝ) (c : ℝ) :
    μ.expect (fun a => (f a - c) ^ 2) =
      μ.variance f + (μ.expect f - c) ^ 2 := by
  let m := μ.expect f
  have hpoint : (fun a => (f a - c) ^ 2) =
      (fun a => (f a - m) ^ 2 +
        (2 * (m - c) * (f a - m) + (m - c) ^ 2)) := by
    funext a
    ring
  rw [hpoint, μ.expect_add, μ.expect_add]
  have hcenter : μ.expect (fun a => f a - m) = 0 := μ.expect_sub_mean f
  have hcross : μ.expect (fun a => 2 * (m - c) * (f a - m)) = 0 := by
    rw [μ.expect_const_mul, hcenter, mul_zero]
  rw [hcross, μ.expect_const, zero_add]
  rfl

theorem variance_le_quarter (μ : FiniteLaw A) (f : A → ℝ)
    (bounded : ∀ a, 0 ≤ f a ∧ f a ≤ 1) : μ.variance f ≤ 1 / 4 := by
  have hpoint : ∀ a, (f a - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
    intro a
    obtain ⟨h0, h1⟩ := bounded a
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have h := μ.expect_mono hpoint
  rw [μ.expect_const, μ.mse_eq_variance_add_sq] at h
  nlinarith [sq_nonneg (μ.expect f - 1 / 2)]

/-- The error event of a scalar estimate is controlled by its mean squared
error. This is the finite-law Chebyshev step needed at a completed tree leaf. -/
theorem square_error_bad_le (μ : FiniteLaw A) (f : A → ℝ) (c e : ℝ)
    (he : 0 ≤ e) :
    e ^ 2 * μ.prob (fun a => e < |f a - c|) ≤
      μ.expect (fun a => (f a - c) ^ 2) := by
  have hsubset : ∀ a, e < |f a - c| → e ^ 2 < (f a - c) ^ 2 := by
    intro a ha
    have habs : 0 ≤ |f a - c| := abs_nonneg _
    nlinarith [sq_abs (f a - c)]
  calc
    e ^ 2 * μ.prob (fun a => e < |f a - c|) ≤
        e ^ 2 * μ.prob (fun a => e ^ 2 < (f a - c) ^ 2) :=
      mul_le_mul_of_nonneg_left (μ.prob_mono hsubset) (sq_nonneg e)
    _ ≤ μ.expect (fun a => (f a - c) ^ 2) :=
      μ.threshold_mul_prob_le _ (fun a => sq_nonneg _) (e ^ 2)

/-- A mean squared error budget gives the scalar exception probability. -/
theorem prob_error_le_of_mse_le (μ : FiniteLaw A) (f : A → ℝ) (c e δ : ℝ)
    (he : 0 < e)
    (hmse : μ.expect (fun a => (f a - c) ^ 2) ≤ e ^ 2 * δ) :
    μ.prob (fun a => e < |f a - c|) ≤ δ := by
  have h := (μ.square_error_bad_le f c e (le_of_lt he)).trans hmse
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  nlinarith

variable {H : Type*} [Fintype H]

/-- A joint failure budget converts to an exceptional set of tables on which
the conditional failure probability is too large. The hash law is independent
of the table law through `FiniteLaw.prod`. -/
theorem tablewise_exception_le (μ : FiniteLaw A) (ν : FiniteLaw H)
    (bad : A → H → Prop) (θ δ : ℝ) (hθ : 0 < θ)
    (hjoint : (μ.prod ν).prob (fun a => bad a.1 a.2) ≤ θ * δ) :
    μ.prob (fun a => θ < ν.prob (bad a)) ≤ δ := by
  have hmarkov := μ.threshold_mul_prob_le
    (fun a => ν.prob (bad a)) (fun a => ν.prob_nonneg (bad a)) θ
  rw [← μ.prob_prod ν bad] at hmarkov
  have h := hmarkov.trans hjoint
  nlinarith

end UnifiedAA.FiniteLaw
