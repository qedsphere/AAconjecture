import UnifiedAA.ConditionalMeans
import UnifiedAA.WeightedPinning

/-! A tree filled with conditional means averages over all unread bits.
The restriction is exactly the set of coordinates on the observed path. -/

namespace UnifiedAA

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem pinBits_insert (P : Finset I) (i : I) (a z : I → Bool) :
    pinBits (insert i P) a z = Function.update (pinBits P a z) i (a i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [pinBits]
  · simp [pinBits, h]

namespace DecisionTree

/-- The distinct coordinates queried when the oracle table is `x`. -/
def pathCoordinates : DecisionTree I → (I → Bool) → Finset I
  | .leaf _, _ => ∅
  | .query i _ zero one, x =>
      insert i (if x i then one.pathCoordinates x else zero.pathCoordinates x)

theorem pathCoordinates_subset (t : DecisionTree I) (x : I → Bool) :
    t.pathCoordinates x ⊆ t.coordinates := by
  induction t with
  | leaf a => simp [pathCoordinates, coordinates]
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;>
        simp only [pathCoordinates, coordinates, hx, Bool.false_eq_true, ↓reduceIte]
      · exact Finset.insert_subset_insert i
          (ih0.trans Finset.subset_union_left)
      · exact Finset.insert_subset_insert i
          (ih1.trans Finset.subset_union_right)

theorem pathCoordinates_card_le_queries (t : DecisionTree I) (x : I → Bool) :
    (t.pathCoordinates x).card ≤ t.queries x := by
  induction t with
  | leaf a => simp [pathCoordinates, queries]
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;>
        simp only [pathCoordinates, queries, hx, Bool.false_eq_true, ↓reduceIte]
      · have h := Finset.card_insert_le i (zero.pathCoordinates x)
        omega
      · have h := Finset.card_insert_le i (one.pathCoordinates x)
        omega

theorem pathCoordinates_withMeans (t : DecisionTree I)
    (f : (I → Bool) → ℝ) (x : I → Bool) :
    (t.withMeans f).pathCoordinates x = t.pathCoordinates x := by
  induction t generalizing f with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      simp only [withMeans, pathCoordinates, ih0, ih1]

/-- Every unread bit is still uniform in this exact leaf-mean formula.
Repeated queries cause no problem because every repeated pin has value `x i`. -/
theorem eval_withMeans_eq_expect_pinBits (t : DecisionTree I)
    (f : (I → Bool) → ℝ) (x : I → Bool) :
    (t.withMeans f).eval x = (FiniteLaw.uniform (I → Bool)).expect
      (fun z => f (pinBits (t.pathCoordinates x) x z)) := by
  induction t generalizing f with
  | leaf a => simp [withMeans, eval, pathCoordinates, pinBits]
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;>
        simp only [withMeans, eval, pathCoordinates, hx, Bool.false_eq_true, ↓reduceIte]
      · rw [ih0]
        apply congrArg ((FiniteLaw.uniform (I → Bool)).expect)
        funext z
        simp only [restrictBit, pinBits_insert, hx]
      · rw [ih1]
        apply congrArg ((FiniteLaw.uniform (I → Bool)).expect)
        funext z
        simp only [restrictBit, pinBits_insert, hx]

theorem summary_withMeans (t : DecisionTree I) (f : (I → Bool) → ℝ) :
    (t.withMeans f).summary = (FiniteLaw.uniform (I → Bool)).expect f := by
  cases t <;> rfl

/-- Refilling summaries depends only on the tree shape and the new target. -/
theorem withMeans_withMeans (t : DecisionTree I) (f g : (I → Bool) → ℝ) :
    (t.withMeans f).withMeans g = t.withMeans g := by
  induction t generalizing f g with
  | leaf a => rfl
  | query i a zero one ih0 ih1 => simp only [withMeans, ih0, ih1]

theorem withMeans_idempotent (t : DecisionTree I) (f : (I → Bool) → ℝ) :
    (t.withMeans f).withMeans f = t.withMeans f :=
  withMeans_withMeans t f f

theorem withMeans_truncate (t : DecisionTree I) (f : (I → Bool) → ℝ) (K : ℕ) :
    (t.withMeans f).truncate K = (t.truncate K).withMeans f := by
  induction K generalizing t f with
  | zero => simp only [truncate, withMeans, summary_withMeans]
  | succ K ih =>
      cases t with
      | leaf a => rfl
      | query i a zero one => simp only [withMeans, truncate, ih]

theorem eval_truncate_withMeans_eq_expect_pinBits (t : DecisionTree I)
    (f : (I → Bool) → ℝ) (K : ℕ) (x : I → Bool) :
    ((t.withMeans f).truncate K).eval x = (FiniteLaw.uniform (I → Bool)).expect
      (fun z => f (pinBits ((t.truncate K).pathCoordinates x) x z)) := by
  rw [withMeans_truncate, eval_withMeans_eq_expect_pinBits]

theorem coordinates_truncate_subset (t : DecisionTree I) (K : ℕ) :
    (t.truncate K).coordinates ⊆ t.coordinates := by
  induction K generalizing t with
  | zero => simp [truncate, coordinates]
  | succ K ih =>
      cases t with
      | leaf a => simp [truncate, coordinates]
      | query i a zero one =>
          exact Finset.insert_subset_insert i
            (Finset.union_subset_union (ih zero) (ih one))

theorem fresh_truncate (t : DecisionTree I) (h : t.Fresh) (K : ℕ) :
    (t.truncate K).Fresh := by
  induction K generalizing t with
  | zero => trivial
  | succ K ih =>
      cases t with
      | leaf a => trivial
      | query i a zero one =>
          obtain ⟨hz, ho, hnz, hno⟩ := h
          exact ⟨ih zero hz, ih one ho,
            fun hi => hnz (coordinates_truncate_subset zero K hi),
            fun hi => hno (coordinates_truncate_subset one K hi)⟩

theorem pathCoordinates_truncate_subset (t : DecisionTree I) (K : ℕ)
    (x : I → Bool) :
    (t.truncate K).pathCoordinates x ⊆ t.pathCoordinates x := by
  induction K generalizing t with
  | zero => simp [truncate, pathCoordinates]
  | succ K ih =>
      cases t with
      | leaf a => simp [truncate, pathCoordinates]
      | query i a zero one =>
          cases hx : x i <;>
            simp only [truncate, pathCoordinates, hx, Bool.false_eq_true, ↓reduceIte]
          · exact Finset.insert_subset_insert i (ih zero)
          · exact Finset.insert_subset_insert i (ih one)

theorem pathCoordinates_card_truncate_le (t : DecisionTree I) (K : ℕ)
    (x : I → Bool) : ((t.truncate K).pathCoordinates x).card ≤ K :=
  (pathCoordinates_card_le_queries (t.truncate K) x).trans
    (queries_truncate_le K t x)

theorem expectedQueries_withMeans (t : DecisionTree I) (f : (I → Bool) → ℝ) :
    (t.withMeans f).expectedQueries = t.expectedQueries := by
  induction t generalizing f with
  | leaf a => rfl
  | query i a zero one ih0 ih1 => simp only [withMeans, expectedQueries, ih0, ih1]

theorem withMeans_hasLeafVariance_of_hasLeafVariance (t : DecisionTree I)
    (f : (I → Bool) → ℝ) (τ : ℝ) (h : t.HasLeafVariance τ f) :
    (t.withMeans f).HasLeafVariance τ f := by
  induction t generalizing f with
  | leaf a => exact ⟨rfl, h.2⟩
  | query i a zero one ih0 ih1 => exact ⟨ih0 _ h.1, ih1 _ h.2⟩

end DecisionTree
end UnifiedAA
