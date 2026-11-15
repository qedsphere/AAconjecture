import UnifiedAA.DecisionTreeUniform
import UnifiedAA.CubeConditioning
import UnifiedAA.ProbabilityBounds

/-! Recursive leaf-error aggregation and deterministic truncation. The tree
construction and its polynomial drift remain explicit separate obligations. -/

namespace UnifiedAA.DecisionTree

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem eval_eq_of_agree (t : DecisionTree I) (x y : I → Bool)
    (agree : ∀ i ∈ t.coordinates, x i = y i) : t.eval x = t.eval y := by
  induction t with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      have hi : x i = y i := agree i (by simp [coordinates])
      have hz := ih0 (fun j hj => agree j (by simp [coordinates, hj]))
      have ho := ih1 (fun j hj => agree j (by simp [coordinates, hj]))
      simp only [eval, hi, hz, ho]

omit [Fintype I] in
theorem eval_update_of_not_mem (t : DecisionTree I) (i : I)
    (hi : i ∉ t.coordinates) (b : Bool) (x : I → Bool) :
    t.eval (Function.update x i b) = t.eval x := by
  apply eval_eq_of_agree
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji _ _

/-- Every leaf returns the exact mean of the target after the branch's
restrictions, and that restricted target has variance at most τ. -/
def HasLeafVariance (τ : ℝ) : DecisionTree I → ((I → Bool) → ℝ) → Prop
  | .leaf a, f => a = (FiniteLaw.uniform (I → Bool)).expect f ∧
      (FiniteLaw.uniform (I → Bool)).variance f ≤ τ
  | .query i _ zero one, f =>
      HasLeafVariance τ zero (restrictBit f i false) ∧
      HasLeafVariance τ one (restrictBit f i true)

theorem mse_query_split (f : (I → Bool) → ℝ) (i : I) (a : ℝ)
    (zero one : DecisionTree I)
    (hz : i ∉ zero.coordinates) (ho : i ∉ one.coordinates) :
    (FiniteLaw.uniform (I → Bool)).expect
      (fun x => (f x - (query i a zero one).eval x) ^ 2) =
      ((FiniteLaw.uniform (I → Bool)).expect
        (fun x => (restrictBit f i false x - zero.eval x) ^ 2) +
       (FiniteLaw.uniform (I → Bool)).expect
        (fun x => (restrictBit f i true x - one.eval x) ^ 2)) / 2 := by
  have h := uniform_expect_restrictBit
    (fun x => (f x - (query i a zero one).eval x) ^ 2) i
  have h0 : restrictBit (fun x => (f x - (query i a zero one).eval x) ^ 2) i false =
      (fun x => (restrictBit f i false x - zero.eval x) ^ 2) := by
    funext x
    simp only [restrictBit, eval, Function.update_self, Bool.false_eq_true,
      ↓reduceIte, eval_update_of_not_mem zero i hz]
  have h1 : restrictBit (fun x => (f x - (query i a zero one).eval x) ^ 2) i true =
      (fun x => (restrictBit f i true x - one.eval x) ^ 2) := by
    funext x
    simp only [restrictBit, eval, Function.update_self, ↓reduceIte,
      eval_update_of_not_mem one i ho]
  rw [h0, h1] at h
  exact h

/-- Averaging over the leaves preserves their common variance budget. -/
theorem mse_le_of_leaf_variance (t : DecisionTree I) (f : (I → Bool) → ℝ)
    (τ : ℝ) (fresh : t.Fresh) (leaves : t.HasLeafVariance τ f) :
    (FiniteLaw.uniform (I → Bool)).expect (fun x => (f x - t.eval x) ^ 2) ≤ τ := by
  induction t generalizing f with
  | leaf a =>
      obtain ⟨ha, hv⟩ := leaves
      simpa only [eval, ha, FiniteLaw.variance] using hv
  | query i a zero one ih0 ih1 =>
      obtain ⟨hz, ho, hnz, hno⟩ := fresh
      obtain ⟨h0, h1⟩ := leaves
      rw [mse_query_split f i a zero one hnz hno]
      have hzero := ih0 (restrictBit f i false) hz h0
      have hone := ih1 (restrictBit f i true) ho h1
      linarith

/-- Chebyshev after aggregation, with no independence assumption on leaves. -/
theorem error_le_of_leaf_variance (t : DecisionTree I) (f : (I → Bool) → ℝ)
    (e δ : ℝ) (he : 0 < e) (fresh : t.Fresh)
    (leaves : t.HasLeafVariance (e ^ 2 * δ) f) :
    (FiniteLaw.uniform (I → Bool)).prob (fun x => e < |f x - t.eval x|) ≤ δ := by
  have hmse := mse_le_of_leaf_variance t f (e ^ 2 * δ) fresh leaves
  simpa only [sub_zero] using
    (FiniteLaw.uniform (I → Bool)).prob_error_le_of_mse_le
      (fun x => f x - t.eval x) 0 e δ he (by simpa only [sub_zero] using hmse)

/-- The scalar-error assembly: leaf error plus the proved potential-based
truncation error, with an actual deterministic K-query bound. -/
theorem truncated_scalar_error (t : DecisionTree I) (f : (I → Bool) → ℝ)
    (e δ : ℝ) (he : 0 < e) (fresh : t.Fresh)
    (leaves : t.HasLeafVariance (e ^ 2 * δ) f)
    (potential : DecisionTree I → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (drift : t.HasDrift potential γ) (K : ℕ) (hK : 0 < K) :
    (∀ x, (t.truncate K).queries x ≤ K) ∧
    (FiniteLaw.uniform (I → Bool)).prob
      (fun x => e < |f x - (t.truncate K).eval x|) ≤
        δ + potential t / (γ * K) := by
  refine ⟨queries_truncate_le K t, ?_⟩
  let μ := FiniteLaw.uniform (I → Bool)
  have hsub : μ.prob (fun x => e < |f x - (t.truncate K).eval x|) ≤
      μ.prob (fun x => e < |f x - t.eval x| ∨ (t.truncate K).eval x ≠ t.eval x) := by
    apply μ.prob_mono
    intro x hx
    by_cases h : (t.truncate K).eval x = t.eval x
    · exact Or.inl (by simpa only [h] using hx)
    · exact Or.inr h
  have hu := μ.prob_union_le
    (fun x => e < |f x - t.eval x|) (fun x => (t.truncate K).eval x ≠ t.eval x)
  have heval := error_le_of_leaf_variance t f e δ he fresh leaves
  have htrunc := uniform_truncation_failure_bound t fresh potential γ hγ drift K hK
  exact hsub.trans (hu.trans (add_le_add heval htrunc))

end UnifiedAA.DecisionTree
