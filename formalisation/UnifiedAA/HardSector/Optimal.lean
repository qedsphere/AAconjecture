import UnifiedAA.HardSector.TreeOps
import UnifiedAA.HardSector.Forward
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Set.Finite.Basic

/-!
# Hard sectors: optimal trees, conditional means, calibration, `ℓ_μ` (HS1.5)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`:
* lines 8-11: `ℓ_μ(t,Q) = min_{D ∈ \mathcal D_t} E_μ|D - Q|` and the squared-loss minimum exist
  (finitely many query structures, continuous loss on a compact cube of leaf outputs);
  `ℓ_μ(·,Q)` is nonincreasing;
* proof of Theorem `ian:hard-sector-regularity`, lines 74-77 and 91-93: an optimal squared-error
  predictor has conditional-mean leaves, `g = E_μ[Q | \mathcal A]` (any value in `[0,1]` on null
  leaves; here `0`), and is calibrated: `E_μ[(Q - g) 1_B] = 0` for `\mathcal A`-measurable `B`;
  Pythagoras for nested leaf partitions.

The leaf partition `\mathcal A` of a tree `T` is encoded by the labelling `leafPath T`; a set or
function is `\mathcal A`-measurable when it factors through `leafPath T`.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- `μ`-conditional mean of `Q` on the cell `{x | c x = p}`; `0` on null cells. -/
noncomputable def cellMean {A : Type*} [Fintype A] (μ : FiniteLaw A) (Q : A → ℝ)
    (c : A → List Bool) (p : List Bool) : ℝ :=
  if 0 < μ.prob (fun x => c x = p) then
    μ.expect (fun x => if c x = p then Q x else 0) / μ.prob (fun x => c x = p)
  else 0

/-- The tree `T` with every leaf output replaced by the `μ`-conditional mean of `Q` on that
leaf's cell: the predictor `E_μ[Q | \mathcal A]` for the leaf partition `\mathcal A` of `T`. -/
noncomputable def condMeanTree {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (T : DecisionTree I) : DecisionTree I :=
  graft T (fun p _ => .leaf (cellMean μ Q (leafPath T) p))

/-- Squared loss `E_μ(Q - D)^2`. -/
def sqLoss {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    (Q : (I → Bool) → ℝ) (D : DecisionTree I) : ℝ :=
  μ.expect (fun x => (Q x - D.eval x) ^ 2)

/-- Absolute loss `E_μ|D - Q|`. -/
def l1Loss {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    (Q : (I → Bool) → ℝ) (D : DecisionTree I) : ℝ :=
  μ.expect (fun x => |D.eval x - Q x|)

/-- `ℓ_μ(t,Q) = min_{D ∈ \mathcal D_t} E_μ|D - Q|` (lines 8-11), defined as an infimum;
`ell_attained` shows the infimum is attained. -/
noncomputable def ell {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    (t : ℕ) (Q : (I → Bool) → ℝ) : ℝ :=
  sInf ((fun D => l1Loss μ Q D) '' DepthTrees I t)
-- LOCK END

/-- The weight of a point is bounded by the mass of its cell. -/
lemma weight_le_cell {A : Type*} [Fintype A] (μ : FiniteLaw A)
    (c : A → List Bool) (x : A) : μ.weight x ≤ μ.prob (fun y => c y = c x) := by
  classical
  unfold FiniteLaw.prob
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun y => if c y = c x then μ.weight y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (Finset.mem_univ x)
  calc
    _ ≤ ∑ y, if c y = c x then μ.weight y else 0 := by simpa using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : c y = c x <;> simp [hy]

lemma cellMean_mem {A : Type*} [Fintype A] (μ : FiniteLaw A)
    {Q : A → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) (c : A → List Bool)
    (p : List Bool) : 0 ≤ cellMean μ Q c p ∧ cellMean μ Q c p ≤ 1 := by
  classical
  unfold cellMean
  split_ifs with hp
  · have hn : 0 ≤ μ.expect (fun x => if c x = p then Q x else 0) := by
      exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x)
        (by dsimp only; split_ifs <;> simp [hQ])
    have hu : μ.expect (fun x => if c x = p then Q x else 0) ≤
        μ.prob (fun x => c x = p) := by
      unfold FiniteLaw.expect FiniteLaw.prob
      apply Finset.sum_le_sum
      intro x _
      dsimp only
      by_cases hx : c x = p
      · simpa [hx] using mul_le_of_le_one_right (μ.nonneg x) (hQ x).2
      · simp [hx]
    exact ⟨div_nonneg hn hp.le, (div_le_one hp).mpr hu⟩
  · exact ⟨le_rfl, zero_le_one⟩

lemma cell_residual_zero {A : Type*} [Fintype A] (μ : FiniteLaw A)
    (Q : A → ℝ) (c : A → List Bool) (p : List Bool) :
    μ.expect (fun x => if c x = p then Q x - cellMean μ Q c p else 0) = 0 := by
  classical
  by_cases hp : 0 < μ.prob (fun x => c x = p)
  · have he : μ.expect (fun x => if c x = p then Q x - cellMean μ Q c p else 0) =
        μ.expect (fun x => if c x = p then Q x else 0) -
          cellMean μ Q c p * μ.prob (fun x => c x = p) := by
      unfold FiniteLaw.expect FiniteLaw.prob
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      dsimp only
      by_cases hx : c x = p
      · simp only [hx, if_true]
        ring
      · simp [hx]
    rw [he, cellMean, if_pos hp, div_mul_cancel₀ _ (ne_of_gt hp), sub_self]
  · have hz : μ.prob (fun x => c x = p) = 0 :=
      le_antisymm (le_of_not_gt hp) (μ.prob_nonneg _)
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : c x = p
    · have hw : μ.weight x = 0 := le_antisymm
        (by simpa [hx, hz] using weight_le_cell μ c x) (μ.nonneg x)
      simp [hw]
    · simp [hx]

/-- Recover the original path from any continuation of it. -/
def decodePath {I : Type*} : DecisionTree I → List Bool → List Bool
  | .leaf _, _ => []
  | .query _ _ _ _, [] => []
  | .query _ _ zero one, b :: bs => b :: decodePath (if b then one else zero) bs

lemma decodePath_append {I : Type*} (T : DecisionTree I) (x : I → Bool)
    (s : List Bool) : decodePath T (leafPath T x ++ s) = leafPath T x := by
  induction T with
  | leaf a => simp [decodePath, leafPath]
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [leafPath, decodePath, hx, ih0, ih1]

/-- Read a leaf answer from a path, using zero for incomplete paths. -/
def pathAnswer {I : Type*} : DecisionTree I → List Bool → ℝ
  | .leaf a, _ => a
  | .query _ _ _ _, [] => 0
  | .query _ _ zero one, b :: bs => pathAnswer (if b then one else zero) bs

lemma pathAnswer_leafPath {I : Type*} (T : DecisionTree I) (x : I → Bool) :
    pathAnswer T (leafPath T x) = T.eval x := by
  induction T with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [leafPath, pathAnswer, DecisionTree.eval, hx, ih0, ih1]

/-- The functions computed by the admissible trees. Query summaries do not affect them. -/
def treeOutputs (I : Type*) (t : ℕ) : Set ((I → Bool) → ℝ) :=
  (fun D : DecisionTree I => D.eval) '' DepthTrees I t

/-- Join two output functions at one coordinate query. -/
def branchOutput {I : Type*} (i : I)
    (fg : ((I → Bool) → ℝ) × ((I → Bool) → ℝ)) (x : I → Bool) : ℝ :=
  if x i then fg.2 x else fg.1 x

lemma treeOutputs_zero (I : Type*) :
    treeOutputs I 0 = (fun a : ℝ => fun _ : I → Bool => a) '' Set.Icc 0 1 := by
  ext f
  constructor
  · rintro ⟨D, hD, rfl⟩
    cases D with
    | leaf a => exact ⟨a, hD.2, rfl⟩
    | query i a zero one =>
        have hd := hD.1
        simp [DecisionTree.depth] at hd
  · rintro ⟨a, ha, rfl⟩
    exact ⟨.leaf a, ⟨le_rfl, ha⟩, rfl⟩

lemma treeOutputs_succ (I : Type*) (t : ℕ) :
    treeOutputs I (t + 1) =
      (fun a : ℝ => fun _ : I → Bool => a) '' Set.Icc 0 1 ∪
      ⋃ i : I, branchOutput i '' (treeOutputs I t ×ˢ treeOutputs I t) := by
  ext f
  constructor
  · rintro ⟨D, hD, rfl⟩
    cases D with
    | leaf a => exact Or.inl ⟨a, hD.2, rfl⟩
    | query i a zero one =>
        have hd := hD.1
        simp only [DecisionTree.depth] at hd
        apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨i, (zero.eval, one.eval), ?_, rfl⟩
        exact ⟨⟨zero, ⟨by omega, hD.2.1⟩, rfl⟩,
          ⟨one, ⟨by omega, hD.2.2⟩, rfl⟩⟩
  · rintro (⟨a, ha, rfl⟩ | hf)
    · exact ⟨.leaf a, ⟨Nat.zero_le _, ha⟩, rfl⟩
    · obtain ⟨i, fg, ⟨⟨zero, hz, hfz⟩, ⟨one, ho, hfo⟩⟩, rfl⟩ :=
        Set.mem_iUnion.mp hf
      rcases fg with ⟨fz, fo⟩
      dsimp only at hfz hfo
      subst fz
      subst fo
      refine ⟨.query i 0 zero one, ⟨?_, hz.2, ho.2⟩, rfl⟩
      simp only [DecisionTree.depth]
      have := hz.1
      have := ho.1
      omega

/-- Depth bounds give a compact family of predictors: constants and finitely many
continuous query combinations of the compact families at the preceding depth. -/
lemma isCompact_treeOutputs (I : Type*) [Fintype I] (t : ℕ) :
    IsCompact (treeOutputs I t) := by
  have hc : IsCompact ((fun a : ℝ => fun _ : I → Bool => a) '' Set.Icc 0 1) :=
    isCompact_Icc.image (continuous_pi fun _ => continuous_id)
  induction t with
  | zero => rw [treeOutputs_zero]; exact hc
  | succ t ih =>
      rw [treeOutputs_succ]
      refine hc.union (isCompact_iUnion fun i => (ih.prod ih).image ?_)
      apply continuous_pi
      intro x
      unfold branchOutput
      cases x i
      · exact (continuous_apply x).comp continuous_fst
      · exact (continuous_apply x).comp continuous_snd

lemma exists_continuous_loss_min {I : Type*} [Fintype I] (t : ℕ)
    (L : ((I → Bool) → ℝ) → ℝ) (hL : Continuous L) :
    ∃ D ∈ DepthTrees I t, ∀ E ∈ DepthTrees I t, L D.eval ≤ L E.eval := by
  have hn : (treeOutputs I t).Nonempty :=
    ⟨_, .leaf 0, ⟨Nat.zero_le _, le_rfl, zero_le_one⟩, rfl⟩
  obtain ⟨f, ⟨D, hD, rfl⟩, hmin⟩ :=
    (isCompact_treeOutputs I t).exists_isMinOn hn hL.continuousOn
  exact ⟨D, hD, fun E hE => hmin ⟨E, hE, rfl⟩⟩

/-- The conditional-mean tree outputs the cell mean of the leaf reached by `T`. -/
theorem eval_condMeanTree {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (T : DecisionTree I) (x : I → Bool) :
    (condMeanTree μ Q T).eval x = cellMean μ Q (leafPath T) (leafPath T x) := by
  simp [condMeanTree, eval_graft, DecisionTree.eval]

/-- For `Q` with values in `[0,1]`, the conditional-mean tree of a tree of depth at most `t`
lies in `\mathcal D_t`. -/
theorem condMeanTree_mem_depthTrees {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) {Q : (I → Bool) → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1)
    {T : DecisionTree I} {t : ℕ} (hT : T.depth ≤ t) :
    condMeanTree μ Q T ∈ DepthTrees I t := by
  obtain ⟨hd, hl⟩ := graft_depth_le_and_leavesIn (P := fun v => 0 ≤ v ∧ v ≤ 1) T
    (fun p _ => .leaf (cellMean μ Q (leafPath T) p)) hT
    (t := 0) (fun p _ => ⟨by simp [DecisionTree.depth], cellMean_mem μ hQ _ p⟩)
  exact ⟨by simpa [condMeanTree] using hd, hl⟩

/-- Proof of Theorem `ian:hard-sector-regularity`, calibration: for `g = E_μ[Q | \mathcal A]`,
`E_μ[(Q - g) h] = 0` for every `\mathcal A`-measurable `h` (in particular `h = 1_B`). -/
theorem expect_resid_mul_eq_zero {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (T : DecisionTree I)
    (h : List Bool → ℝ) :
    μ.expect (fun x => (Q x - (condMeanTree μ Q T).eval x) * h (leafPath T x)) = 0 := by
  classical
  let c := leafPath T
  let ps := Finset.univ.image c
  have hf : ∀ p, μ.expect (fun x => if c x = p then
      (Q x - cellMean μ Q c (c x)) * h (c x) else 0) = 0 := by
    intro p
    have he : (fun x => if c x = p then
        (Q x - cellMean μ Q c (c x)) * h (c x) else 0) =
        (fun x => h p * (if c x = p then Q x - cellMean μ Q c p else 0)) := by
      funext x
      by_cases hx : c x = p <;> simp [hx, mul_comm]
    rw [he, μ.expect_const_mul, cell_residual_zero, mul_zero]
  simp_rw [eval_condMeanTree]
  change μ.expect (fun x => (Q x - cellMean μ Q c (c x)) * h (c x)) = 0
  calc
    _ = ∑ p ∈ ps, μ.expect (fun x => if c x = p then
        (Q x - cellMean μ Q c (c x)) * h (c x) else 0) := by
      unfold FiniteLaw.expect
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_eq_single (c x)]
      · simp
      · intro p _ hp
        simp [Ne.symm hp]
      · intro hx
        exact False.elim (hx (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
    _ = 0 := by simp [hf]

/-- Proof of Theorem `ian:hard-sector-regularity`, Pythagoras: for every
`\mathcal A`-measurable `f`, `E_μ(Q - f)^2 = E_μ(Q - g)^2 + E_μ(g - f)^2` with
`g = E_μ[Q | \mathcal A]`. -/
theorem sq_pythagoras {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (T : DecisionTree I)
    (f : List Bool → ℝ) :
    μ.expect (fun x => (Q x - f (leafPath T x)) ^ 2) =
      sqLoss μ Q (condMeanTree μ Q T) +
        μ.expect (fun x => ((condMeanTree μ Q T).eval x - f (leafPath T x)) ^ 2) := by
  have hz := expect_resid_mul_eq_zero μ Q T
    (fun p => cellMean μ Q (leafPath T) p - f p)
  have he : (fun x => (Q x - f (leafPath T x)) ^ 2) =
      (fun x => (Q x - (condMeanTree μ Q T).eval x) ^ 2 +
        ((condMeanTree μ Q T).eval x - f (leafPath T x)) ^ 2 +
        2 * ((Q x - (condMeanTree μ Q T).eval x) *
          (cellMean μ Q (leafPath T) (leafPath T x) - f (leafPath T x)))) := by
    funext x
    rw [eval_condMeanTree]
    ring
  rw [he, μ.expect_add, μ.expect_add, μ.expect_const_mul, hz, mul_zero, add_zero]
  rfl

/-- Proof of Theorem `ian:hard-sector-regularity`, nested partitions: the leaf partition of
`graft T k` refines that of `T`, i.e. every function of `leafPath T` is a function of
`leafPath (graft T k)`. -/
theorem exists_factor_leafPath_graft {I : Type*} (T : DecisionTree I)
    (k : List Bool → ℝ → DecisionTree I) (f : List Bool → ℝ) :
    ∃ f' : List Bool → ℝ, ∀ x, f (leafPath T x) = f' (leafPath (graft T k) x) := by
  refine ⟨fun p => f (decodePath T p), ?_⟩
  intro x
  simp only [leafPath_graft, decodePath_append]

/-- A tree's output is a function of its leaf path (it is `\mathcal A`-measurable for its own
leaf partition). -/
theorem exists_eval_eq_comp_leafPath {I : Type*} (D : DecisionTree I) :
    ∃ φ : List Bool → ℝ, ∀ x, D.eval x = φ (leafPath D x) := by
  exact ⟨pathAnswer D, fun x => (pathAnswer_leafPath D x).symm⟩

/-- The conditional-mean tree has the same leaf partition as `T`. -/
theorem leafPath_condMeanTree {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (T : DecisionTree I) (x : I → Bool) :
    leafPath (condMeanTree μ Q T) x = leafPath T x := by
  simp [condMeanTree, leafPath_graft, leafPath]

/-- Definition `ian:hard-sector-definition`: `E_{μ(·|H)} f = E_μ[f 1_H] / μ(H)`. -/
theorem expect_condLaw {A : Type*} [Fintype A] (μ : FiniteLaw A) (H : Set A)
    (hH : 0 < μ.prob (· ∈ H)) (f : A → ℝ) :
    (condLaw μ H hH).expect f = μ.expect (H.indicator f) / μ.prob (· ∈ H) := by
  classical
  unfold FiniteLaw.expect condLaw
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ H
  · simp only [hx, if_true, Set.indicator_of_mem]
    ring
  · simp [hx]

/-- Lines 8-11 and proof of Theorem `ian:hard-sector-regularity`: the squared-loss minimum
over `\mathcal D_t` is attained by a conditional-mean tree `condMeanTree μ Q T` with
`T.depth ≤ t` (which lies in `\mathcal D_t` when `Q ∈ [0,1]`, by
`condMeanTree_mem_depthTrees`). -/
theorem exists_sqLoss_min {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (t : ℕ) :
    ∃ T : DecisionTree I, T.depth ≤ t ∧
      ∀ D ∈ DepthTrees I t, sqLoss μ Q (condMeanTree μ Q T) ≤ sqLoss μ Q D := by
  have hc : Continuous (fun f : (I → Bool) → ℝ =>
      μ.expect (fun x => (Q x - f x) ^ 2)) := by
    unfold FiniteLaw.expect
    exact continuous_finsetSum _ fun x _ =>
      continuous_const.mul ((continuous_const.sub (continuous_apply x)).pow 2)
  obtain ⟨T, hT, hmin⟩ := exists_continuous_loss_min t _ hc
  obtain ⟨φ, hφ⟩ := exists_eval_eq_comp_leafPath T
  have hp := sq_pythagoras μ Q T φ
  have he : (fun x => (Q x - φ (leafPath T x)) ^ 2) =
      (fun x => (Q x - T.eval x) ^ 2) := by
    funext x
    rw [← hφ]
  rw [he] at hp
  have hn : 0 ≤ μ.expect (fun x =>
      ((condMeanTree μ Q T).eval x - φ (leafPath T x)) ^ 2) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _)
  refine ⟨T, hT.1, fun D hD => ?_⟩
  have hm := hmin D hD
  change sqLoss μ Q T ≤ sqLoss μ Q D at hm
  change sqLoss μ Q T = _ at hp
  linarith

/-- Lines 8-11: `ℓ_μ(t,Q)` is attained: some `D ∈ \mathcal D_t` has `E_μ|D - Q| = ℓ_μ(t,Q)`,
and `ℓ_μ(t,Q) ≤ E_μ|D' - Q|` for every `D' ∈ \mathcal D_t`. -/
theorem ell_attained {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (t : ℕ) :
    (∃ D ∈ DepthTrees I t, l1Loss μ Q D = ell μ t Q) ∧
      ∀ D ∈ DepthTrees I t, ell μ t Q ≤ l1Loss μ Q D := by
  have hc : Continuous (fun f : (I → Bool) → ℝ =>
      μ.expect (fun x => |f x - Q x|)) := by
    unfold FiniteLaw.expect
    exact continuous_finsetSum _ fun x _ =>
      continuous_const.mul (((continuous_apply x).sub continuous_const).abs)
  obtain ⟨D, hD, hmin⟩ := exists_continuous_loss_min t _ hc
  change ∀ E ∈ DepthTrees I t, l1Loss μ Q D ≤ l1Loss μ Q E at hmin
  have hb : BddBelow ((fun E => l1Loss μ Q E) '' DepthTrees I t) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨E, _, rfl⟩
    exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (abs_nonneg _)
  have hle : ∀ E ∈ DepthTrees I t, ell μ t Q ≤ l1Loss μ Q E :=
    fun E hE => csInf_le hb ⟨E, hE, rfl⟩
  refine ⟨⟨D, hD, le_antisymm ?_ (hle D hD)⟩, hle⟩
  unfold ell
  apply le_csInf (s := (fun E => l1Loss μ Q E) '' DepthTrees I t) ⟨_, D, hD, rfl⟩
  rintro _ ⟨E, hE, rfl⟩
  exact hmin E hE

/-- Lines 8-11: `ℓ_μ(·,Q)` is nonincreasing. -/
theorem ell_antitone {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) {t t' : ℕ} (htt' : t ≤ t') :
    ell μ t' Q ≤ ell μ t Q := by
  obtain ⟨⟨D, hD, he⟩, _⟩ := ell_attained μ Q t
  rw [← he]
  exact (ell_attained μ Q t').2 D (depthTrees_mono htt' hD)

/-- `ℓ_μ(t,Q) ≤ ε` iff some `D ∈ \mathcal D_t` has `E_μ|D - Q| ≤ ε` (the encoding used in
`AAWith`). -/
theorem ell_le_iff {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (t : ℕ) (ε : ℝ) :
    ell μ t Q ≤ ε ↔ ∃ D ∈ DepthTrees I t, l1Loss μ Q D ≤ ε := by
  constructor
  · intro h
    obtain ⟨⟨D, hD, he⟩, _⟩ := ell_attained μ Q t
    exact ⟨D, hD, he.trans_le h⟩
  · rintro ⟨D, hD, hε⟩
    exact ((ell_attained μ Q t).2 D hD).trans hε

end UnifiedAA.HardSector
