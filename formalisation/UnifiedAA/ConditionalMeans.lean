import UnifiedAA.ScalarError

namespace UnifiedAA.DecisionTree

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Fill every stored summary with the exact mean of the restricted target.
The queried coordinates and branching shape are preserved. -/
noncomputable def withMeans : DecisionTree I → ((I → Bool) → ℝ) → DecisionTree I
  | .leaf _, f => .leaf ((FiniteLaw.uniform (I → Bool)).expect f)
  | .query i _ zero one, f =>
      .query i ((FiniteLaw.uniform (I → Bool)).expect f)
        (withMeans zero (restrictBit f i false)) (withMeans one (restrictBit f i true))

theorem withMeans_coordinates (t : DecisionTree I) (f : (I → Bool) → ℝ) :
    (t.withMeans f).coordinates = t.coordinates := by
  induction t generalizing f with
  | leaf a => rfl
  | query i a zero one ih0 ih1 => simp only [withMeans, coordinates, ih0, ih1]

theorem withMeans_fresh (t : DecisionTree I) (f : (I → Bool) → ℝ)
    (h : t.Fresh) : (t.withMeans f).Fresh := by
  induction t generalizing f with
  | leaf a => trivial
  | query i a zero one ih0 ih1 =>
      obtain ⟨hz, ho, hnz, hno⟩ := h
      exact ⟨ih0 _ hz, ih1 _ ho,
        by simpa only [withMeans_coordinates] using hnz,
        by simpa only [withMeans_coordinates] using hno⟩

theorem withMeans_queries (t : DecisionTree I) (f : (I → Bool) → ℝ) (x : I → Bool) :
    (t.withMeans f).queries x = t.queries x := by
  induction t generalizing f with
  | leaf a => rfl
  | query i a zero one ih0 ih1 => simp only [withMeans, queries, ih0, ih1]

/-- A condition on the target variances at the leaves, independent of the
original tree's stored real summaries. -/
def LowVarianceLeaves (τ : ℝ) : DecisionTree I → ((I → Bool) → ℝ) → Prop
  | .leaf _, f => (FiniteLaw.uniform (I → Bool)).variance f ≤ τ
  | .query i _ zero one, f =>
      LowVarianceLeaves τ zero (restrictBit f i false) ∧
      LowVarianceLeaves τ one (restrictBit f i true)

theorem withMeans_hasLeafVariance (t : DecisionTree I) (f : (I → Bool) → ℝ)
    (τ : ℝ) (h : t.LowVarianceLeaves τ f) :
    (t.withMeans f).HasLeafVariance τ f := by
  induction t generalizing f with
  | leaf a => exact ⟨rfl, h⟩
  | query i a zero one ih0 ih1 => exact ⟨ih0 _ h.1, ih1 _ h.2⟩

/-- An actual deterministic conditional-mean estimator on any fresh query
shape whose terminal restrictions have sufficiently small variance. -/
theorem withMeans_error (t : DecisionTree I) (f : (I → Bool) → ℝ)
    (e δ : ℝ) (he : 0 < e) (fresh : t.Fresh)
    (leaves : t.LowVarianceLeaves (e ^ 2 * δ) f) :
    (FiniteLaw.uniform (I → Bool)).prob
      (fun x => e < |f x - (t.withMeans f).eval x|) ≤ δ :=
  error_le_of_leaf_variance _ f e δ he (withMeans_fresh t f fresh)
    (withMeans_hasLeafVariance t f _ leaves)

end UnifiedAA.DecisionTree
