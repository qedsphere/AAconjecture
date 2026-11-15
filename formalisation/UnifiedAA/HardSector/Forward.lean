import UnifiedAA.HardSector.Basic

/-!
# Hard sectors: the forward bound (HS1.3)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, Proposition
`ian:hard-sector-forward` (H1-forward) and its proof.

Stated per tree: for every `D ∈ \mathcal D_t`, `E_μ|Q - D| ≥ w(a - γ)`. Minimising over `D`
gives the TeX form `ℓ_μ(t,Q) ≥ w(a - γ)`.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

/-- Evaluation selects a leaf, so it preserves any predicate on leaf outputs. -/
lemma eval_mem_of_leavesIn {I : Type*} {P : ℝ → Prop} {D : DecisionTree I}
    (hD : LeavesIn P D) (x : I → Bool) : P (D.eval x) := by
  induction D with
  | leaf v => exact hD
  | query i s zero one ih0 ih1 =>
      cases hx : x i <;> simp [DecisionTree.eval, hx, ih0 hD.1, ih1 hD.2]

/-- Expand squared prediction loss around the mean of the target. -/
lemma sq_loss_eq_variance_add {A : Type*} [Fintype A] (ν : FiniteLaw A)
    (Q D : A → ℝ) :
    ν.expect (fun x => (Q x - D x) ^ 2) = ν.variance Q +
      ν.expect (fun x => (D x - ν.expect Q) ^ 2) - 2 * cov ν Q D := by
  have hpoint : (fun x => (Q x - D x) ^ 2) =
      (fun x => (Q x - ν.expect Q) ^ 2 + (D x - ν.expect Q) ^ 2 +
        (-2) * ((Q x - ν.expect Q) * D x) +
        (2 * ν.expect Q) * (Q x - ν.expect Q)) := by
    funext x
    ring
  rw [hpoint, ν.expect_add, ν.expect_add, ν.expect_add,
    ν.expect_const_mul, ν.expect_const_mul, ν.expect_sub_mean,
    expect_centered_mul_eq_cov]
  change ν.variance Q + _ + (-2) * cov ν Q D + (2 * ν.expect Q) * 0 = _
  ring

/-- Proof of Proposition `ian:hard-sector-forward`, first step: if `Hard(Q,ν;t,a,γ)` then
`E_ν(Q - D)^2 ≥ a - γ` for every `D ∈ \mathcal D_t`. -/
theorem sq_loss_ge_of_hard {I : Type*} [Fintype I] [DecidableEq I]
    {Q : (I → Bool) → ℝ} {ν : FiniteLaw (I → Bool)} {t : ℕ} {a γ : ℝ}
    (h : Hard Q ν t a γ) {D : DecisionTree I} (hD : D ∈ DepthTrees I t) :
    a - γ ≤ ν.expect (fun x => (Q x - D.eval x) ^ 2) := by
  have hcov := (covCondition_iff Q ν t γ).mp h.2.2.2.2 D hD
  have hcov_upper : cov ν Q D.eval ≤ γ / 2 := (le_abs_self _).trans hcov
  have hnonneg : 0 ≤ ν.expect (fun x => (D.eval x - ν.expect Q) ^ 2) := by
    calc
      0 = ν.expect (fun _ => (0 : ℝ)) := (ν.expect_const 0).symm
      _ ≤ _ := ν.expect_mono (fun x => sq_nonneg _)
  rw [sq_loss_eq_variance_add]
  linarith [h.2.2.2.1]

/-- Proposition `ian:hard-sector-forward` (H1-forward), per tree: if `Q` takes values in
`[0,1]` and `ν` is a smooth sector of `μ` of weight `w` with `Hard(Q,ν;t,a,γ)`, then
`E_μ|Q - D| ≥ w(a - γ)` for every `D ∈ \mathcal D_t`. -/
theorem forward_bound {I : Type*} [Fintype I] [DecidableEq I]
    {μ ν : FiniteLaw (I → Bool)} {Q : (I → Bool) → ℝ} {t : ℕ} {a γ w : ℝ}
    (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) (hS : IsSmoothSector μ ν Q t a γ w)
    {D : DecisionTree I} (hD : D ∈ DepthTrees I t) :
    w * (a - γ) ≤ μ.expect (fun x => |Q x - D.eval x|) := by
  obtain ⟨hw, _, hdom, hhard⟩ := hS
  have hpoint : ∀ x, (Q x - D.eval x) ^ 2 ≤ |Q x - D.eval x| := by
    intro x
    obtain ⟨hD0, hD1⟩ := eval_mem_of_leavesIn hD.2 x
    obtain ⟨hQ0, hQ1⟩ := hQ x
    have habs : |Q x - D.eval x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hmul := mul_le_mul_of_nonneg_left habs (abs_nonneg (Q x - D.eval x))
    nlinarith [sq_abs (Q x - D.eval x)]
  calc
    w * (a - γ) ≤ w * ν.expect (fun x => (Q x - D.eval x) ^ 2) :=
      mul_le_mul_of_nonneg_left (sq_loss_ge_of_hard hhard hD) hw.le
    _ = ∑ x, (w * ν.weight x) * (Q x - D.eval x) ^ 2 := by
      unfold FiniteLaw.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ μ.expect (fun x => |Q x - D.eval x|) := by
      apply Finset.sum_le_sum
      intro x _
      calc
        (w * ν.weight x) * (Q x - D.eval x) ^ 2 ≤
            (w * ν.weight x) * |Q x - D.eval x| :=
          mul_le_mul_of_nonneg_left (hpoint x) (mul_nonneg hw.le (ν.nonneg x))
        _ ≤ μ.weight x * |Q x - D.eval x| :=
          mul_le_mul_of_nonneg_right (hdom x) (abs_nonneg _)

end UnifiedAA.HardSector
