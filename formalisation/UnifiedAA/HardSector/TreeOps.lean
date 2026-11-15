import UnifiedAA.HardSector.Basic

/-!
# Hard sectors: tree aggregation and extremal tests (HS1.2)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, Lemma `ian:hard-sector-tree-closure`.

* Sequential composition: run `T`, then a tree selected by the leaf reached (identified by the
  answers along the path, `leafPath`, and the leaf output). Depth at most `s + t`.
* A function of the outputs of `k` trees of depth at most `t` is computed by a tree of depth at
  most `k * t`, with leaves in any output range containing the function's values.
* Extremal tests: the covariance condition over `\mathcal F_t` is equivalent to the same
  condition over trees with leaf outputs in `{-1,1}`.

The count `N(n,t)` is not formalised here.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- The answers read along the path that `T` follows on input `x`, root first. Together with the
leaf output it identifies the leaf reached. -/
def leafPath {I : Type*} : DecisionTree I → (I → Bool) → List Bool
  | .leaf _, _ => []
  | .query i _ zero one, x => x i :: (if x i then leafPath one x else leafPath zero x)

/-- Sequential composition: run `T`; at the leaf with path `p` and output `a`, continue with the
tree `k p a`. -/
def graft {I : Type*} : DecisionTree I → (List Bool → ℝ → DecisionTree I) → DecisionTree I
  | .leaf a, k => k [] a
  | .query i s zero one, k =>
      .query i s (graft zero (fun p => k (false :: p))) (graft one (fun p => k (true :: p)))

/-- Trees of depth at most `t` with leaf outputs in `{-1,1}` (the extremal tests of Lemma
`ian:hard-sector-tree-closure`). -/
def ExtremalTrees (I : Type*) (t : ℕ) : Set (DecisionTree I) :=
  {F | F.depth ≤ t ∧ LeavesIn (fun v => v = -1 ∨ v = 1) F}
-- LOCK END

/-- Lemma `ian:hard-sector-tree-closure`: the grafted tree runs `T` and then the tree selected by
the leaf reached. -/
theorem eval_graft {I : Type*} (T : DecisionTree I) (k : List Bool → ℝ → DecisionTree I)
    (x : I → Bool) :
    (graft T k).eval x = (k (leafPath T x) (T.eval x)).eval x := by
  induction T generalizing k with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [graft, leafPath, DecisionTree.eval, hx, ih0, ih1]

/-- Lemma `ian:hard-sector-tree-closure`: the path of the grafted tree is the path of `T`
followed by the path of the selected tree (so the leaf partition of the graft refines that
of `T`). -/
theorem leafPath_graft {I : Type*} (T : DecisionTree I) (k : List Bool → ℝ → DecisionTree I)
    (x : I → Bool) :
    leafPath (graft T k) x = leafPath T x ++ leafPath (k (leafPath T x) (T.eval x)) x := by
  induction T generalizing k with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [graft, leafPath, DecisionTree.eval, hx, ih0, ih1]

/-- Lemma `ian:hard-sector-tree-closure` (sequential composition): a depth-`s` tree followed by
depth-`t` trees selected by the leaf reached has depth at most `s + t`, and its leaves are leaves
of the selected trees. -/
theorem graft_depth_le_and_leavesIn {I : Type*} {s t : ℕ} {P : ℝ → Prop}
    (T : DecisionTree I) (k : List Bool → ℝ → DecisionTree I) (hT : T.depth ≤ s)
    (hk : ∀ p a, (k p a).depth ≤ t ∧ LeavesIn P (k p a)) :
    (graft T k).depth ≤ s + t ∧ LeavesIn P (graft T k) := by
  have h : (graft T k).depth ≤ T.depth + t ∧ LeavesIn P (graft T k) := by
    clear hT s
    induction T generalizing k with
    | leaf a => simpa [graft, DecisionTree.depth] using hk [] a
    | query i a zero one ih0 ih1 =>
        obtain ⟨hz, hPz⟩ := ih0 (fun p => k (false :: p)) (fun p a => hk _ a)
        obtain ⟨ho, hPo⟩ := ih1 (fun p => k (true :: p)) (fun p a => hk _ a)
        refine ⟨?_, hPz, hPo⟩
        simp only [graft, DecisionTree.depth]
        omega
  exact ⟨h.1.trans (Nat.add_le_add_right hT t), h.2⟩

/-- Sequentially evaluate a finite tuple of trees, with no restriction on leaf answers. -/
lemma exists_tree_of_function_unrestricted {I : Type*} {k t : ℕ}
    (Ts : Fin k → DecisionTree I) (hTs : ∀ j, (Ts j).depth ≤ t)
    (φ : (Fin k → ℝ) → ℝ) :
    ∃ D : DecisionTree I, D.depth ≤ k * t ∧
      ∀ x, D.eval x = φ (fun j => (Ts j).eval x) := by
  classical
  induction k with
  | zero =>
      refine ⟨.leaf (φ Fin.elim0), by simp [DecisionTree.depth], ?_⟩
      intro x
      change φ Fin.elim0 = φ _
      congr 1
      funext j
      exact Fin.elim0 j
  | succ k ih =>
      have htail : ∀ a : ℝ, ∃ D : DecisionTree I, D.depth ≤ k * t ∧
          ∀ x, D.eval x = φ (Fin.cons a (fun j => (Ts j.succ).eval x)) :=
        fun a => ih (fun j => Ts j.succ) (fun j => hTs j.succ) (fun v => φ (Fin.cons a v))
      choose Ds hDs using htail
      refine ⟨graft (Ts 0) (fun _ a => Ds a), ?_, ?_⟩
      · have hd := (graft_depth_le_and_leavesIn (P := fun _ => True) (Ts 0)
            (fun _ a => Ds a) (hTs 0) (fun _ a => ⟨(hDs a).1, ?_⟩)).1
        · simpa [Nat.succ_mul, Nat.add_comm] using hd
        · induction Ds a with
          | leaf _ => trivial
          | query _ _ _ _ hz ho => exact ⟨hz, ho⟩
      · intro x
        rw [eval_graft, (hDs _).2]
        congr 1
        funext j
        refine Fin.cases ?_ (fun j => ?_) j <;> rfl

/-- Replace unreachable leaves by the output at a fixed input. This preserves evaluation
and depth bounds while enforcing any predicate satisfied by every evaluated output. -/
lemma exists_tree_with_leavesIn {I : Type*} (T : DecisionTree I) (P : ℝ → Prop)
    (hP : ∀ x, P (T.eval x)) :
    ∃ D : DecisionTree I, D.depth ≤ T.depth ∧ LeavesIn P D ∧
      ∀ x, D.eval x = T.eval x := by
  classical
  let x0 : I → Bool := fun _ => false
  let k : List Bool → ℝ → DecisionTree I := fun p a =>
    .leaf (if ∃ x, leafPath T x = p ∧ T.eval x = a then a else T.eval x0)
  have hk : ∀ p a, (k p a).depth ≤ 0 ∧ LeavesIn P (k p a) := by
    intro p a
    refine ⟨by simp [k, DecisionTree.depth], ?_⟩
    change P (if ∃ x, leafPath T x = p ∧ T.eval x = a then a else T.eval x0)
    split_ifs with h
    · obtain ⟨x, _, hx⟩ := h
      rw [← hx]
      exact hP x
    · exact hP x0
  obtain ⟨hd, hl⟩ := graft_depth_le_and_leavesIn T k (le_refl _) hk
  refine ⟨graft T k, by simpa using hd, hl, ?_⟩
  intro x
  rw [eval_graft]
  change (if ∃ y, leafPath T y = leafPath T x ∧ T.eval y = T.eval x
    then T.eval x else T.eval x0) = T.eval x
  exact if_pos ⟨x, rfl, rfl⟩

/-- Lemma `ian:hard-sector-tree-closure` (aggregation): any function `φ` of the outputs of `k`
trees of depth at most `t`, whose values on all inputs satisfy the output-range predicate `P`,
is computed by a tree of depth at most `k * t` with leaves satisfying `P`. -/
theorem exists_tree_of_function {I : Type*} {k t : ℕ} (Ts : Fin k → DecisionTree I)
    (hTs : ∀ j, (Ts j).depth ≤ t) (P : ℝ → Prop) (φ : (Fin k → ℝ) → ℝ)
    (hφ : ∀ x, P (φ (fun j => (Ts j).eval x))) :
    ∃ D : DecisionTree I, D.depth ≤ k * t ∧ LeavesIn P D ∧
      ∀ x, D.eval x = φ (fun j => (Ts j).eval x) := by
  obtain ⟨T, hd, he⟩ := exists_tree_of_function_unrestricted Ts hTs φ
  obtain ⟨D, hD, hP, hEval⟩ := exists_tree_with_leavesIn T P (fun x => by rw [he]; exact hφ x)
  exact ⟨D, hD.trans hd, hP, fun x => (hEval x).trans (he x)⟩

/-- Lemma `ian:hard-sector-tree-closure`: `ExtremalTrees I t ⊆ SignTrees I t`. -/
theorem extremalTrees_subset_signTrees {I : Type*} (t : ℕ) :
    ExtremalTrees I t ⊆ SignTrees I t := by
  intro F hF
  refine ⟨hF.1, ?_⟩
  have h := hF.2
  clear hF
  induction F with
  | leaf a => rcases h with h | h <;> simp_all [LeavesIn]
  | query i a zero one ih0 ih1 => exact ⟨ih0 h.1, ih1 h.2⟩

/-- Split an arbitrary weighted sum at the root query. Weights may have either sign. -/
lemma sum_eval_query {I : Type*} [Fintype I] [DecidableEq I] (g : (I → Bool) → ℝ)
    (i : I) (a : ℝ) (zero one : DecisionTree I) :
    (∑ x, g x * (DecisionTree.query i a zero one).eval x) =
      (∑ x, (if x i then 0 else g x) * zero.eval x) +
      (∑ x, (if x i then g x else 0) * one.eval x) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : x i <;> simp [DecisionTree.eval, hx]

/-- A linear functional on the leaf answers is maximized at extremal answers. -/
lemma exists_extremal_ge {I : Type*} [Fintype I] [DecidableEq I] (F : DecisionTree I)
    (hF : LeavesIn (fun v => -1 ≤ v ∧ v ≤ 1) F) (g : (I → Bool) → ℝ) :
    ∃ E : DecisionTree I, E.depth ≤ F.depth ∧
      LeavesIn (fun v => v = -1 ∨ v = 1) E ∧
      (∑ x, g x * F.eval x) ≤ ∑ x, g x * E.eval x := by
  classical
  induction F generalizing g with
  | leaf a =>
      by_cases hg : 0 ≤ ∑ x, g x
      · refine ⟨.leaf 1, le_refl _, Or.inr rfl, ?_⟩
        simpa only [DecisionTree.eval, ← Finset.sum_mul] using
          mul_le_mul_of_nonneg_left hF.2 hg
      · refine ⟨.leaf (-1), le_refl _, Or.inl rfl, ?_⟩
        simpa only [DecisionTree.eval, ← Finset.sum_mul] using
          mul_le_mul_of_nonpos_left hF.1 (le_of_not_ge hg)
  | query i a zero one ih0 ih1 =>
      obtain ⟨E0, hd0, hl0, hs0⟩ := ih0 hF.1 (fun x => if x i then 0 else g x)
      obtain ⟨E1, hd1, hl1, hs1⟩ := ih1 hF.2 (fun x => if x i then g x else 0)
      refine ⟨.query i a E0 E1, ?_, ⟨hl0, hl1⟩, ?_⟩
      · simp only [DecisionTree.depth]
        omega
      · rw [sum_eval_query, sum_eval_query]
        exact add_le_add hs0 hs1

/-- Lemma `ian:hard-sector-tree-closure` (extremal tests): for any law `ν`, checking
`|E_ν[(Q - m_ν) F]| ≤ γ` for all `F ∈ \mathcal F_t` is equivalent to checking it for the trees of
depth at most `t` with leaf outputs in `{-1,1}`. -/
theorem covCondition_iff_extremal {I : Type*} [Fintype I] [DecidableEq I]
    (Q : (I → Bool) → ℝ) (ν : FiniteLaw (I → Bool)) (t : ℕ) (γ : ℝ) :
    CovCondition Q ν t γ ↔
      ∀ F ∈ ExtremalTrees I t, |ν.expect (fun x => (Q x - ν.expect Q) * F.eval x)| ≤ γ := by
  constructor
  · intro h F hF
    exact h F (extremalTrees_subset_signTrees t hF)
  · intro h F hF
    let g : (I → Bool) → ℝ := fun x => ν.weight x * (Q x - ν.expect Q)
    have heq : ∀ D : DecisionTree I,
        ν.expect (fun x => (Q x - ν.expect Q) * D.eval x) = ∑ x, g x * D.eval x := by
      intro D
      unfold FiniteLaw.expect
      apply Finset.sum_congr rfl
      intro x _
      dsimp [g, FiniteLaw.expect]
      ring
    obtain ⟨Ep, hdp, hlp, hsp⟩ := exists_extremal_ge F hF.2 g
    obtain ⟨Em, hdm, hlm, hsm⟩ := exists_extremal_ge F hF.2 (fun x => -g x)
    have hp := h Ep ⟨hdp.trans hF.1, hlp⟩
    have hm := h Em ⟨hdm.trans hF.1, hlm⟩
    rw [heq] at hp hm ⊢
    simp only [neg_mul, Finset.sum_neg_distrib] at hsm
    apply abs_le.mpr
    constructor
    · linarith [(abs_le.mp hm).1]
    · exact hsp.trans (abs_le.mp hp).2

end UnifiedAA.HardSector
