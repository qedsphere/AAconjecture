import UnifiedAA.DecisionTree
import UnifiedAA.Uniform

/-! Fresh oracle queries are fair branches under a uniformly random table.
This discharges the fairness hypothesis of the general truncation theorem. -/

namespace UnifiedAA.DecisionTree

variable {I : Type*} [DecidableEq I]

def coordinates : DecisionTree I → Finset I
  | .leaf _ => ∅
  | .query i _ zero one => insert i (zero.coordinates ∪ one.coordinates)

/-- Every queried coordinate is absent from both descendant subtrees. -/
def Fresh : DecisionTree I → Prop
  | .leaf _ => True
  | .query i _ zero one =>
      zero.Fresh ∧ one.Fresh ∧ i ∉ zero.coordinates ∧ i ∉ one.coordinates

theorem queries_eq_of_agree (t : DecisionTree I) (x y : I → Bool)
    (agree : ∀ i ∈ t.coordinates, x i = y i) : t.queries x = t.queries y := by
  induction t with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      have hi : x i = y i := agree i (by simp [coordinates])
      have hz : zero.queries x = zero.queries y :=
        ih0 (fun j hj => agree j (by simp [coordinates, hj]))
      have ho : one.queries x = one.queries y :=
        ih1 (fun j hj => agree j (by simp [coordinates, hj]))
      simp only [queries, hi, hz, ho]

theorem queries_flip_of_not_mem (t : DecisionTree I) (i : I)
    (hi : i ∉ t.coordinates) (x : I → Bool) :
    t.queries (flip i x) = t.queries x := by
  apply queries_eq_of_agree
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  exact Function.update_of_ne hji _ _

/-- Exact connection between operational physical query cost and the
fair-branch recurrence, valid for fresh-coordinate trees. -/
theorem uniform_expected_queries [Fintype I] (t : DecisionTree I) (fresh : t.Fresh) :
    (FiniteLaw.uniform (I → Bool)).expect (fun x => (t.queries x : ℝ)) =
      t.expectedQueries := by
  induction t with
  | leaf a => simp [queries, expectedQueries, FiniteLaw.expect]
  | query i a zero one ih0 ih1 =>
      obtain ⟨hz, ho, hnz, hno⟩ := fresh
      have hzero := ih0 hz
      have hone := ih1 ho
      have hbranch := uniform_expect_branch i
        (fun x => (zero.queries x : ℝ)) (fun x => (one.queries x : ℝ))
        (fun x => by rw [queries_flip_of_not_mem zero i hnz x])
        (fun x => by rw [queries_flip_of_not_mem one i hno x])
      have hfun : (fun x => ((DecisionTree.query i a zero one).queries x : ℝ)) =
          (fun x => 1 + if x i then (one.queries x : ℝ) else (zero.queries x : ℝ)) := by
        funext x
        simp only [queries, Nat.cast_add, Nat.cast_one]
        cases x i <;> rfl
      rw [hfun, FiniteLaw.expect_add, FiniteLaw.expect_const, hbranch, hzero, hone]
      rfl

/-- A deterministic K-query truncation preserves the original tree on all
but potential(root)/(gamma*K) uniformly random Boolean oracle tables. -/
theorem uniform_truncation_failure_bound [Fintype I]
    (t : DecisionTree I) (fresh : t.Fresh)
    (potential : DecisionTree I → ℝ) (gamma : ℝ) (hgamma : 0 < gamma)
    (drift : t.HasDrift potential gamma) (K : ℕ) (hK : 0 < K) :
    (FiniteLaw.uniform (I → Bool)).prob
      (fun x => (t.truncate K).eval x ≠ t.eval x) ≤ potential t / (gamma * K) :=
  truncation_failure_bound _ t potential gamma hgamma drift
    (uniform_expected_queries t fresh) K hK

end UnifiedAA.DecisionTree
