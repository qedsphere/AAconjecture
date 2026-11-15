import UnifiedAA.ProbabilityBounds

/-! Bounded scalar error implies a large deviation of an estimator from the
original mean. The leaf interpretation is supplied separately by query trees. -/

namespace UnifiedAA.FiniteLaw
variable {X : Type*} [Fintype X]

theorem expect_mem_unit (μ : FiniteLaw X) (f : X → ℝ)
    (bounded : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ μ.expect f ∧ μ.expect f ≤ 1 := by
  constructor
  · simpa only [μ.expect_const] using μ.expect_mono (fun x => (bounded x).1)
  · simpa only [μ.expect_const] using μ.expect_mono (fun x => (bounded x).2)

theorem mse_le_of_error_probability (μ : FiniteLaw X) (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (e δ : ℝ) (he : 0 ≤ e)
    (error : μ.prob (fun x => e < |f x - g x|) ≤ δ) :
    μ.expect (fun x => (f x - g x) ^ 2) ≤ e ^ 2 + δ := by
  classical
  have hpoint (x : X) : (f x - g x) ^ 2 ≤
      e ^ 2 + (if e < |f x - g x| then 1 else 0) := by
    have hb : |f x - g x| ≤ 1 := abs_le.mpr ⟨by linarith [(hf x).1, (hg x).2],
      by linarith [(hf x).2, (hg x).1]⟩
    by_cases h : e < |f x - g x|
    · rw [if_pos h]
      nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x), sq_nonneg e]
    · rw [if_neg h]
      have hn := le_of_not_gt h
      nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x)]
  have h := μ.expect_mono hpoint
  rw [μ.expect_add, μ.expect_const] at h
  have hi : μ.expect (fun x => if e < |f x - g x| then 1 else 0) =
      μ.prob (fun x => e < |f x - g x|) := by
    unfold expect prob
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [hi] at h
  linarith

theorem abs_error_square_le_mse (μ : FiniteLaw X) (f g : X → ℝ) :
    (μ.expect (fun x => |f x - g x|)) ^ 2 ≤
      μ.expect (fun x => (f x - g x) ^ 2) := by
  have h := μ.mse_eq_variance_add_sq (fun x => |f x - g x|) 0
  simp only [sub_zero, sq_abs] at h
  linarith [μ.variance_nonneg (fun x => |f x - g x|)]

theorem variance_le_deviation_add_error (μ : FiniteLaw X) (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    μ.variance f ≤ μ.expect (fun x => |g x - μ.expect f|) +
      μ.expect (fun x => |f x - g x|) := by
  obtain ⟨hm0, hm1⟩ := μ.expect_mem_unit f hf
  have hs (x : X) : (f x - μ.expect f) ^ 2 ≤ |f x - μ.expect f| := by
    have hb : |f x - μ.expect f| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
    nlinarith [sq_abs (f x - μ.expect f), abs_nonneg (f x - μ.expect f)]
  have ht (x : X) : |f x - μ.expect f| ≤
      |g x - μ.expect f| + |f x - g x| := by
    simpa only [add_comm] using abs_sub_le (f x) (g x) (μ.expect f)
  have h := (μ.expect_mono hs).trans (μ.expect_mono ht)
  rw [μ.expect_add] at h
  exact h

theorem exists_expect_le [Nonempty X] (μ : FiniteLaw X) (f : X → ℝ) :
    ∃ x, μ.expect f ≤ f x := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨x, ?_⟩
  simpa only [μ.expect_const] using μ.expect_mono (fun y => hx y (Finset.mem_univ y))

/-- The numerical step of Proposition 2.6, with the paper's exact parameters. -/
theorem exists_biased_value [Nonempty X] (μ : FiniteLaw X) (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (v : ℝ) (hv : 0 < v) (variance : μ.variance f = v)
    (error : μ.prob (fun x => v / 8 < |f x - g x|) ≤ v ^ 2 / 32) :
    ∃ x, 3 * v / 4 ≤ |g x - μ.expect f| := by
  have hmse := μ.mse_le_of_error_probability f g hf hg (v / 8) (v ^ 2 / 32)
    (by positivity) error
  have hsq := μ.abs_error_square_le_mse f g
  have hsmall : μ.expect (fun x => |f x - g x|) ≤ v / 4 := by
    nlinarith
  have hdev := μ.variance_le_deviation_add_error f g hf
  rw [variance] at hdev
  obtain ⟨x, hx⟩ := μ.exists_expect_le (fun x => |g x - μ.expect f|)
  exact ⟨x, by linarith⟩

end UnifiedAA.FiniteLaw
