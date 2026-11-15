import UnifiedAA.InfluenceTree

/-! Scalar polynomial simulation from a quantified influence bound. -/

namespace UnifiedAA

/-- The precise fixed-threshold consequence needed from AA, uniformly over
all bounded degree-d polynomials, including their restrictions. -/
def PolynomialInfluenceRule (N d : ℕ) (τ γ : ℝ) : Prop :=
  ∀ p : MvPolynomial (Fin N) ℝ, p.totalDegree ≤ d →
    (∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) →
    τ < (FiniteLaw.uniform (Fin N → Bool)).variance (cubeEval p) →
    ∃ i, γ ≤ cubeFlipInfluence (cubeEval p) i

namespace DecisionTree

theorem exists_polynomial_tree {N d : ℕ} {τ γ : ℝ} (hγ : 0 < γ)
    (rule : PolynomialInfluenceRule N d τ γ) (p : MvPolynomial (Fin N) ℝ)
    (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) :
    ∃ t : DecisionTree (Fin N), t.Fresh ∧ t.HasLeafVariance τ (cubeEval p) ∧
      γ * t.expectedQueries ≤ d := by
  let P := fun f : (Fin N → Bool) → ℝ =>
    ∃ q : MvPolynomial (Fin N) ℝ, q.totalDegree ≤ d ∧
      (∀ x, 0 ≤ cubeEval q x ∧ cubeEval q x ≤ 1) ∧ f = cubeEval q
  have closed : ∀ f, P f → ∀ i b, P (restrictBit f i b) := by
    rintro f ⟨q, hq, hb, rfl⟩ i b
    exact ⟨restrictPolynomial q i b, restrictPolynomial_degree_le hq i b,
      cubeEval_restrictPolynomial_bounded q hb i b, (cubeEval_restrict q i b).symm⟩
  have choose : ∀ f, P f → τ < (FiniteLaw.uniform (Fin N → Bool)).variance f →
      ∃ i, γ ≤ cubeFlipInfluence f i := by
    rintro f ⟨q, hq, hb, rfl⟩ hv
    exact rule q hq hb hv
  obtain ⟨t, ht, _, hv, hc⟩ := exists_of_influence_rule P τ γ hγ closed choose
    Finset.univ (cubeEval p) ⟨p, degree, bounded, rfl⟩
    (fun x y h => congrArg (cubeEval p) (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨t, ht, hv, hc.trans (cubeEval_totalFlipInfluence_le p degree bounded)⟩

theorem truncation_failure_of_cost {I : Type*} [Fintype I] [DecidableEq I]
    (t : DecisionTree I) (fresh : t.Fresh) (γ C : ℝ) (hγ : 0 < γ)
    (cost : γ * t.expectedQueries ≤ C) (K : ℕ) (hK : 0 < K) :
    (FiniteLaw.uniform (I → Bool)).prob
      (fun x => (t.truncate K).eval x ≠ t.eval x) ≤ C / (γ * K) := by
  let μ := FiniteLaw.uniform (I → Bool)
  have hm := μ.threshold_mul_prob_le (fun x => (t.queries x : ℝ))
    (fun x => by positivity) (K : ℝ)
  rw [uniform_expected_queries t fresh] at hm
  have hsub : μ.prob (fun x => (t.truncate K).eval x ≠ t.eval x) ≤
      μ.prob (fun x => (K : ℝ) < (t.queries x : ℝ)) := by
    apply μ.prob_mono
    intro x hx
    have hn : K < t.queries x := Nat.lt_of_not_ge
      (fun h => hx (eval_truncate_eq_of_queries_le K t x h))
    exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  apply (le_div_iff₀ (mul_pos hγ hK')).mpr
  calc
    _ = γ * ((K : ℝ) * μ.prob (fun x => (t.truncate K).eval x ≠ t.eval x)) := by ring
    _ ≤ γ * t.expectedQueries := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hsub (le_of_lt hK')).trans hm) (le_of_lt hγ)
    _ ≤ C := cost

/-- An actual deterministic K-query estimator with its uniform-table error
bound, assuming the stated polynomial influence rule. -/
theorem exists_polynomial_estimator {N d : ℕ} (e δ γ : ℝ) (he : 0 < e) (hγ : 0 < γ)
    (rule : PolynomialInfluenceRule N d (e ^ 2 * δ) γ)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (K : ℕ) (hK : 0 < K) :
    ∃ t : DecisionTree (Fin N), (∀ x, t.queries x ≤ K) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |cubeEval p x - t.eval x|) ≤ δ + d / (γ * K) := by
  obtain ⟨t, ht, hv, hc⟩ := exists_polynomial_tree hγ rule p degree bounded
  refine ⟨t.truncate K, queries_truncate_le K t, ?_⟩
  let μ := FiniteLaw.uniform (Fin N → Bool)
  have hsub : μ.prob (fun x => e < |cubeEval p x - (t.truncate K).eval x|) ≤
      μ.prob (fun x => e < |cubeEval p x - t.eval x| ∨ (t.truncate K).eval x ≠ t.eval x) := by
    apply μ.prob_mono
    intro x hx
    by_cases h : (t.truncate K).eval x = t.eval x
    · exact Or.inl (by simpa only [h] using hx)
    · exact Or.inr h
  exact hsub.trans ((μ.prob_union_le _ _).trans (add_le_add
    (error_le_of_leaf_variance t (cubeEval p) e δ he ht hv)
    (truncation_failure_of_cost t ht γ d hγ hc K hK)))

end DecisionTree
end UnifiedAA
