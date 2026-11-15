import UnifiedAA.Influence
import UnifiedAA.PolynomialSimulation

/-! AA-guided scalar simulation for bounded real polynomials.
The imported AA statement is an explicit parameter; instantiating it with
the pinned upstream `aaronson_ambainis` is a separate integration checkpoint.
This theorem constructs deterministic query trees, not merely estimators
assumed to have a prescribed cost. -/

namespace UnifiedAA

theorem aa_polynomial_influence_rule
    (hAA : AaronsonAmbainis.PrintedConjecture) (N d : ℕ) (hd : 1 ≤ d)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    PolynomialInfluenceRule N d τ (τ ^ 8 / (d : ℝ) ^ 12) := by
  intro p degree bounded hv
  obtain ⟨i, hi⟩ := coarse_influence_bound hAA N d p degree bounded hd τ hτ hτ1
    (by rw [cubeVariance_eq_uniform_variance]; exact le_of_lt hv)
  exact ⟨i, by simpa only [flipInfluence_eq_cubeFlipInfluence] using hi⟩

/-- The polynomial scalar simulator, with explicit rounding-independent
budget condition. Error and failure parameters lie in (0,1]. -/
theorem exists_aa_scalar_estimator
    (hAA : AaronsonAmbainis.PrintedConjecture) {N d : ℕ} (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (K : ℕ) (hK : 0 < K)
    (budget : 2 * (d : ℝ) ≤ δ * ((e ^ 2 * (δ / 2)) ^ 8 / (d : ℝ) ^ 12) * K) :
    ∃ t : DecisionTree (Fin N), (∀ x, t.queries x ≤ K) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |cubeEval p x - t.eval x|) ≤ δ := by
  let τ := e ^ 2 * (δ / 2)
  let γ := τ ^ 8 / (d : ℝ) ^ 12
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have he2 : e ^ 2 ≤ 1 := by nlinarith
  have hτ1 : τ ≤ 1 := by dsimp [τ]; nlinarith [sq_nonneg e]
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨t, hqueries, herror⟩ := DecisionTree.exists_polynomial_estimator e (δ / 2) γ he hγ
    (aa_polynomial_influence_rule hAA N d hd τ hτ hτ1) p degree bounded K hK
  refine ⟨t, hqueries, herror.trans ?_⟩
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hratio : (d : ℝ) / (γ * K) ≤ δ / 2 := by
    apply (div_le_iff₀ (mul_pos hγ hK')).mpr
    change 2 * (d : ℝ) ≤ δ * γ * K at budget
    nlinarith
  linarith

/-- Explicit integer budget for the manuscript's degree/error exponents. -/
noncomputable def scalarQueryBudget (d : ℕ) (e δ : ℝ) : ℕ :=
  ⌈(512 : ℝ) * (d : ℝ) ^ 13 / (e ^ 16 * δ ^ 9)⌉₊

theorem exists_aa_scalar_estimator_explicit
    (hAA : AaronsonAmbainis.PrintedConjecture) {N d : ℕ} (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N), (∀ x, t.queries x ≤ scalarQueryBudget d e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |cubeEval p x - t.eval x|) ≤ δ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  apply exists_aa_scalar_estimator hAA hd p degree bounded e δ he he1 hδ hδ1
  · unfold scalarQueryBudget
    apply Nat.ceil_pos.mpr
    positivity
  · have hden : 0 < δ * ((e ^ 2 * (δ / 2)) ^ 8 / (d : ℝ) ^ 12) := by positivity
    have halgebra :
        2 * (d : ℝ) / (δ * ((e ^ 2 * (δ / 2)) ^ 8 / (d : ℝ) ^ 12)) =
          512 * (d : ℝ) ^ 13 / (e ^ 16 * δ ^ 9) := by
      field_simp
      <;> ring
    have hceil := Nat.le_ceil (512 * (d : ℝ) ^ 13 / (e ^ 16 * δ ^ 9))
    rw [← halgebra] at hceil
    have hb := (div_le_iff₀ hden).mp hceil
    rw [halgebra] at hb
    change 2 * (d : ℝ) ≤ _ * (scalarQueryBudget d e δ : ℝ)
    simpa only [scalarQueryBudget, mul_comm] using hb

end UnifiedAA
