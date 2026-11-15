import UnifiedAA.MeanRestriction
import UnifiedAA.RestrictionRisk
import UnifiedAA.ScalarSimulation

/-! The AA simulator can return actual conditional means at every leaf.
Its scalar error bound therefore supplies a restriction with a biased mean. -/

namespace UnifiedAA

/-- The scalar simulator with exact conditional means, including at leaves
created by truncation. The influence rule constructs the underlying tree. -/
theorem exists_aa_scalar_mean_estimator
    (hAA : AaronsonAmbainis.PrintedConjecture) {N d : ℕ} (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (K : ℕ) (hK : 0 < K)
    (budget : 2 * (d : ℝ) ≤ δ * ((e ^ 2 * (δ / 2)) ^ 8 / (d : ℝ) ^ 12) * K) :
    ∃ t : DecisionTree (Fin N), t.Fresh ∧ (∀ x, t.queries x ≤ K) ∧
      (∀ x, t.eval x = (FiniteLaw.uniform (Fin N → Bool)).expect
        (fun z => cubeEval p (pinBits (t.pathCoordinates x) x z))) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |cubeEval p x - t.eval x|) ≤ δ := by
  let τ := e ^ 2 * (δ / 2)
  let γ := τ ^ 8 / (d : ℝ) ^ 12
  let μ := FiniteLaw.uniform (Fin N → Bool)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have he2 : e ^ 2 ≤ 1 := by nlinarith
  have hτ1 : τ ≤ 1 := by dsimp [τ]; nlinarith [sq_nonneg e]
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨t, ht, hv, hc⟩ := DecisionTree.exists_polynomial_tree hγ
    (aa_polynomial_influence_rule hAA N d hd τ hτ hτ1) p degree bounded
  let m := t.withMeans (cubeEval p)
  have hmFresh : m.Fresh := DecisionTree.withMeans_fresh t _ ht
  have hmVar : m.HasLeafVariance τ (cubeEval p) :=
    DecisionTree.withMeans_hasLeafVariance_of_hasLeafVariance t _ τ hv
  have hmCost : γ * m.expectedQueries ≤ d := by
    simpa only [m, DecisionTree.expectedQueries_withMeans] using hc
  refine ⟨m.truncate K, DecisionTree.fresh_truncate m hmFresh K,
    DecisionTree.queries_truncate_le K m, ?_, ?_⟩
  · intro x
    simpa only [m, DecisionTree.withMeans_truncate,
      DecisionTree.pathCoordinates_withMeans] using
      DecisionTree.eval_withMeans_eq_expect_pinBits (t.truncate K) (cubeEval p) x
  · have hsub : μ.prob (fun x => e < |cubeEval p x - (m.truncate K).eval x|) ≤
        μ.prob (fun x => e < |cubeEval p x - m.eval x| ∨
          (m.truncate K).eval x ≠ m.eval x) := by
      apply μ.prob_mono
      intro x hx
      by_cases h : (m.truncate K).eval x = m.eval x
      · exact Or.inl (by simpa only [h] using hx)
      · exact Or.inr h
    have herror := DecisionTree.error_le_of_leaf_variance m (cubeEval p)
      e (δ / 2) he hmFresh hmVar
    have htrunc := DecisionTree.truncation_failure_of_cost m hmFresh γ d
      hγ hmCost K hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hratio : (d : ℝ) / (γ * K) ≤ δ / 2 := by
      apply (div_le_iff₀ (mul_pos hγ hK')).mpr
      change 2 * (d : ℝ) ≤ δ * γ * K at budget
      nlinarith
    have htotal := hsub.trans ((μ.prob_union_le _ _).trans
      (add_le_add herror htrunc))
    exact htotal.trans (by linarith)

/-- Exact conditional means cost the same explicit number of queries as
the scalar estimator. -/
theorem exists_aa_scalar_mean_estimator_explicit
    (hAA : AaronsonAmbainis.PrintedConjecture) {N d : ℕ} (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N), t.Fresh ∧
      (∀ x, t.queries x ≤ scalarQueryBudget d e δ) ∧
      (∀ x, t.eval x = (FiniteLaw.uniform (Fin N → Bool)).expect
        (fun z => cubeEval p (pinBits (t.pathCoordinates x) x z))) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |cubeEval p x - t.eval x|) ≤ δ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  apply exists_aa_scalar_mean_estimator hAA hd p degree bounded e δ he he1 hδ hδ1
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

/-- Proposition 2.6 for any bounded degree-d Boolean-cube polynomial.
The unpinned coordinates are averaged under the actual uniform law. -/
theorem exists_aa_biased_restriction
    (hAA : AaronsonAmbainis.PrintedConjecture) {N d : ℕ} (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (v : ℝ) (hv : 0 < v)
    (variance : (FiniteLaw.uniform (Fin N → Bool)).variance (cubeEval p) = v) :
    ∃ (J : Finset (Fin N)) (a : Fin N → Bool),
      J.card ≤ scalarQueryBudget d (v / 8) (v ^ 2 / 32) ∧
      3 * v / 4 ≤ |(FiniteLaw.uniform (Fin N → Bool)).expect
        (fun z => cubeEval p (pinBits J a z)) -
        (FiniteLaw.uniform (Fin N → Bool)).expect (cubeEval p)| := by
  let μ := FiniteLaw.uniform (Fin N → Bool)
  have hvquarter : v ≤ 1 / 4 := by
    rw [← variance]
    exact μ.variance_le_quarter (cubeEval p) bounded
  have he : 0 < v / 8 := by positivity
  have he1 : v / 8 ≤ 1 := by linarith
  have hδ : 0 < v ^ 2 / 32 := by positivity
  have hδ1 : v ^ 2 / 32 ≤ 1 := by nlinarith
  obtain ⟨t, _, hqueries, hmean, herror⟩ := exists_aa_scalar_mean_estimator_explicit
    hAA hd p degree bounded (v / 8) (v ^ 2 / 32) he he1 hδ hδ1
  have hbounded : ∀ x, 0 ≤ t.eval x ∧ t.eval x ≤ 1 := by
    intro x
    rw [hmean x]
    exact μ.expect_mem_unit _ (fun z => bounded _)
  obtain ⟨a, ha⟩ := μ.exists_biased_value (cubeEval p) t.eval bounded hbounded
    v hv variance herror
  refine ⟨t.pathCoordinates a, a,
    (DecisionTree.pathCoordinates_card_le_queries t a).trans (hqueries a), ?_⟩
  simpa only [hmean a] using ha

theorem scalarQueryBudget_restriction (d : ℕ) (v : ℝ) (hv : 0 < v) :
    scalarQueryBudget d (v / 8) (v ^ 2 / 32) =
      ⌈(512 : ℝ) * 2 ^ 93 * (d : ℝ) ^ 13 / v ^ 34⌉₊ := by
  unfold scalarQueryBudget
  congr 1
  field_simp [ne_of_gt hv]
  <;> ring

end UnifiedAA
