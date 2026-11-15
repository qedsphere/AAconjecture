import UnifiedAA.FiniteProbability

/-!
# Deterministic Boolean-oracle decision trees

Queries carry a real summary used when the tree is truncated. No randomness
occurs in evaluation. Expected query counts below initially refer to fair
branches; their equality to uniform-oracle expectations requires freshness.
-/

namespace UnifiedAA

inductive DecisionTree (I : Type*) where
  | leaf (answer : ℝ)
  | query (coordinate : I) (summary : ℝ) (zero one : DecisionTree I)

namespace DecisionTree

variable {I : Type*}

def summary : DecisionTree I → ℝ
  | .leaf a => a
  | .query _ a _ _ => a

def eval : DecisionTree I → (I → Bool) → ℝ
  | .leaf a, _ => a
  | .query i _ zero one, x => if x i then one.eval x else zero.eval x

def queries : DecisionTree I → (I → Bool) → ℕ
  | .leaf _, _ => 0
  | .query i _ zero one, x => 1 + if x i then one.queries x else zero.queries x

def depth : DecisionTree I → ℕ
  | .leaf _ => 0
  | .query _ _ zero one => 1 + max zero.depth one.depth

theorem queries_le_depth (t : DecisionTree I) (x : I → Bool) :
    t.queries x ≤ t.depth := by
  induction t with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      simp only [queries, depth]
      cases x i <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · omega
      · omega

/-- Stop at the stored summary after at most K physical bit queries. -/
def truncate : ℕ → DecisionTree I → DecisionTree I
  | 0, t => .leaf t.summary
  | _ + 1, .leaf a => .leaf a
  | K + 1, .query i a zero one => .query i a (truncate K zero) (truncate K one)

theorem depth_truncate_le (K : ℕ) (t : DecisionTree I) :
    (t.truncate K).depth ≤ K := by
  induction K generalizing t with
  | zero => simp [truncate, depth]
  | succ K ih =>
      cases t with
      | leaf a => simp [truncate, depth]
      | query i a zero one =>
          simp only [truncate, depth]
          have h0 := ih zero
          have h1 := ih one
          omega

theorem queries_truncate_le (K : ℕ) (t : DecisionTree I) (x : I → Bool) :
    (t.truncate K).queries x ≤ K :=
  (queries_le_depth _ _).trans (depth_truncate_le _ _)

theorem eval_truncate_eq_of_queries_le (K : ℕ) (t : DecisionTree I) (x : I → Bool)
    (h : t.queries x ≤ K) : (t.truncate K).eval x = t.eval x := by
  induction K generalizing t with
  | zero =>
      cases t with
      | leaf a => rfl
      | query i a zero one => simp [queries] at h
  | succ K ih =>
      cases t with
      | leaf a => rfl
      | query i a zero one =>
          cases hx : x i <;> simp only [queries, hx, Bool.false_eq_true, ↓reduceIte] at h
          · simpa [truncate, eval, hx] using ih zero (by omega)
          · simpa [truncate, eval, hx] using ih one (by omega)

/-- Expected query count under independently fair branches. -/
noncomputable def expectedQueries : DecisionTree I → ℝ
  | .leaf _ => 0
  | .query _ _ zero one => 1 + (zero.expectedQueries + one.expectedQueries) / 2

theorem expectedQueries_nonneg (t : DecisionTree I) : 0 ≤ t.expectedQueries := by
  induction t with
  | leaf a => simp [expectedQueries]
  | query i a zero one ih0 ih1 => dsimp [expectedQueries]; linarith

/-- Nonnegative potential at every leaf, with expected drop at least gamma
at every query. A terminal potential need not be zero. -/
def HasDrift (potential : DecisionTree I → ℝ) (gamma : ℝ) : DecisionTree I → Prop
  | .leaf a => 0 ≤ potential (.leaf a)
  | .query i a zero one =>
      HasDrift potential gamma zero ∧ HasDrift potential gamma one ∧
      gamma + (potential zero + potential one) / 2 ≤ potential (.query i a zero one)

/-- Finite-tree telescoping; no optional stopping theorem is needed. -/
theorem expectedQueries_mul_le_potential (t : DecisionTree I)
    (potential : DecisionTree I → ℝ) (gamma : ℝ) (h : t.HasDrift potential gamma) :
    gamma * t.expectedQueries ≤ potential t := by
  induction t with
  | leaf a => simpa [expectedQueries, HasDrift] using h
  | query i a zero one ih0 ih1 =>
      obtain ⟨h0, h1, hdrop⟩ := h
      have hz := ih0 h0
      have ho := ih1 h1
      dsimp [expectedQueries]
      nlinarith

/-- General truncation bound under a finite table law. The equality of the
table expectation to fair-branch cost is an explicit hypothesis here. -/
theorem truncation_failure_bound [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (t : DecisionTree I)
    (potential : DecisionTree I → ℝ) (gamma : ℝ)
    (hgamma : 0 < gamma) (drift : t.HasDrift potential gamma)
    (fair : μ.expect (fun x => (t.queries x : ℝ)) = t.expectedQueries)
    (K : ℕ) (hK : 0 < K) :
    μ.prob (fun x => (t.truncate K).eval x ≠ t.eval x) ≤ potential t / (gamma * K) := by
  have hmono : μ.prob (fun x => (t.truncate K).eval x ≠ t.eval x) ≤
      μ.prob (fun x => (K : ℝ) < (t.queries x : ℝ)) := by
    apply μ.prob_mono
    intro x hx
    have hn : ¬ t.queries x ≤ K := fun h => hx (eval_truncate_eq_of_queries_le K t x h)
    exact_mod_cast Nat.lt_of_not_ge hn
  have hmarkov := μ.threshold_mul_prob_le (fun x => (t.queries x : ℝ))
    (fun x => by positivity) (K : ℝ)
  rw [fair] at hmarkov
  have hcost := expectedQueries_mul_le_potential t potential gamma drift
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  apply (le_div_iff₀ (mul_pos hgamma hK')).2
  calc
    _ = gamma * ((K : ℝ) * μ.prob (fun x => (t.truncate K).eval x ≠ t.eval x)) := by ring
    _ ≤ gamma * t.expectedQueries :=
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hmono (le_of_lt hK')).trans hmarkov)
        (le_of_lt hgamma)
    _ ≤ potential t := hcost

end DecisionTree
end UnifiedAA
