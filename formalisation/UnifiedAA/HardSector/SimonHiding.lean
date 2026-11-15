import UnifiedAA.HardSector.SimonPosterior
import UnifiedAA.HardSector.TreeOps

/-!
# Simon law: adaptive transcript hiding (HS3.3)

Source: `notes/ian/30_simon_sector.tex`, Lemma `ian:simon-adaptive-posterior` (the adaptive
collision bound and (30.1)) and Corollary `ian:simon-bit-hiding` (lines 164-286).

Deterministic adaptive coordinate strategies are bit decision trees on the table coordinates
`Fin (m * 2^m)` (the repo's `DecisionTree`); a strategy of depth at most `t` touches at most `t`
arguments. With `c_t = C(t, 2)`, `N = M - 1` and `η_t = 2c_t/(N - c_t)` (assuming `c_t < N`):
* (30.1), bit-transcript form: `Σ_τ |E_μ[(Y - ρ_m) 1_{τ}]| ≤ η_t`, the sum over the leaf
  transcripts `τ` (leaf paths) of the tree; this is `E|E[Y | τ_bit] - ρ_m| ≤ η_t`;
* `|Cov_μ(Y, F)| ≤ η_t` for `F ∈ \mathcal F_t` and `|Cov_μ(Y, D)| ≤ η_t/2` for `D ∈ \mathcal D_t`.
The whole-output form of (30.1) is the special case of trees that read whole labels; it is used
inside the proof, not stated separately.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

open scoped Classical

/-- The total absolute centered mass at the leaves, defined by tree recursion. -/
noncomputable def simonPotential {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) : DecisionTree I → ((I → Bool) → ℝ) → ℝ
  | .leaf _, g => |μ.expect g|
  | .query i _ zero one, g =>
      simonPotential μ zero (fun X => if X i = false then g X else 0) +
      simonPotential μ one (fun X => if X i = true then g X else 0)

private lemma hiding_expect_sum {A B : Type*} [Fintype A] (μ : FiniteLaw A)
    (s : Finset B) (g : B → A → ℝ) :
    μ.expect (fun X => ∑ b ∈ s, g b X) = ∑ b ∈ s, μ.expect (g b) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

@[simp] lemma simonPotential_zero {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (T : DecisionTree I) :
    simonPotential μ T (fun _ => 0) = 0 := by
  induction T with
  | leaf a => simp [simonPotential, FiniteLaw.expect]
  | query i a zero one ih0 ih1 => simp [simonPotential, ih0, ih1]

lemma simonPotential_sum_le {I B : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (T : DecisionTree I)
    (s : Finset B) (g : B → (I → Bool) → ℝ) :
    simonPotential μ T (fun X => ∑ b ∈ s, g b X) ≤
      ∑ b ∈ s, simonPotential μ T (g b) := by
  induction T generalizing g with
  | leaf a =>
      simp only [simonPotential, hiding_expect_sum]
      exact Finset.abs_sum_le_sum_abs _ _
  | query i a zero one ih0 ih1 =>
      have hf (b : Bool) :
          (fun X => if X i = b then ∑ k ∈ s, g k X else 0) =
          (fun X => ∑ k ∈ s, if X i = b then g k X else 0) := by
        funext X
        by_cases h : X i = b <;> simp [h]
      simp only [simonPotential, hf, Finset.sum_add_distrib]
      exact add_le_add (ih0 _) (ih1 _)

lemma simonPotential_le_abs {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (T : DecisionTree I) (g : (I → Bool) → ℝ) :
    simonPotential μ T g ≤ μ.expect (fun X => |g X|) := by
  induction T generalizing g with
  | leaf a =>
      calc
        _ ≤ ∑ X, |μ.weight X * g X| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp [FiniteLaw.expect, abs_mul, abs_of_nonneg (μ.nonneg _)]
  | query i a zero one ih0 ih1 =>
      calc
        _ ≤ μ.expect (fun X => |if X i = false then g X else 0|) +
            μ.expect (fun X => |if X i = true then g X else 0|) :=
          add_le_add (ih0 _) (ih1 _)
        _ = _ := by
          rw [← μ.expect_add]
          congr 1
          funext X
          cases X i <;> simp

/-- All structural leaf paths, including paths made unreachable by repeated queries. -/
def simonTreePaths {I : Type*} : DecisionTree I → Finset (List Bool)
  | .leaf _ => {[]}
  | .query _ _ zero one =>
      (simonTreePaths zero).image (false :: ·) ∪ (simonTreePaths one).image (true :: ·)

lemma leafPath_mem_simonTreePaths {I : Type*} (T : DecisionTree I) (X : I → Bool) :
    leafPath T X ∈ simonTreePaths T := by
  induction T with
  | leaf a => simp [leafPath, simonTreePaths]
  | query i a zero one ih0 ih1 =>
      cases h : X i <;> simp [leafPath, simonTreePaths, h, ih0, ih1]

lemma simonPotential_eq_paths {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (T : DecisionTree I) (g : (I → Bool) → ℝ) :
    simonPotential μ T g = ∑ p ∈ simonTreePaths T,
      |μ.expect (fun X => if leafPath T X = p then g X else 0)| := by
  induction T generalizing g with
  | leaf a => simp [simonPotential, simonTreePaths, leafPath]
  | query i a zero one ih0 ih1 =>
      have hd : Disjoint ((simonTreePaths zero).image (false :: ·))
          ((simonTreePaths one).image (true :: ·)) := by
        simp [Finset.disjoint_left]
      rw [simonPotential, simonTreePaths, Finset.sum_union hd,
        Finset.sum_image (by simp),
        Finset.sum_image (by simp), ih0, ih1]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro p hp <;>
        congr 2 <;> funext X <;> cases h : X i <;> simp [leafPath, h]

lemma simonPotential_eq_transcripts {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (T : DecisionTree I) (g : (I → Bool) → ℝ) :
    simonPotential μ T g = ∑ p ∈ Finset.univ.image (leafPath T),
      |μ.expect (fun X => if leafPath T X = p then g X else 0)| := by
  rw [simonPotential_eq_paths]
  symm
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨X, _, rfl⟩ := Finset.mem_image.mp hp
    exact leafPath_mem_simonTreePaths T X
  · intro p hp hn
    have h (X : I → Bool) : leafPath T X ≠ p := by
      intro he
      exact hn (Finset.mem_image.mpr ⟨X, Finset.mem_univ _, he⟩)
    simp [h, FiniteLaw.expect]

lemma simonPotential_eval_le {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (T : DecisionTree I)
    (hT : LeavesIn (fun v => -1 ≤ v ∧ v ≤ 1) T) (g : (I → Bool) → ℝ) :
    |μ.expect (fun X => g X * T.eval X)| ≤ simonPotential μ T g := by
  induction T generalizing g with
  | leaf a =>
      have ha : |a| ≤ 1 := abs_le.mpr hT
      have he : μ.expect (fun X => g X * a) = μ.expect g * a := by
        simp [FiniteLaw.expect, mul_assoc, Finset.sum_mul]
      change |μ.expect (fun X => g X * a)| ≤ |μ.expect g|
      rw [he, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) ha
  | query i a zero one ih0 ih1 =>
      have he : μ.expect (fun X => g X * (DecisionTree.query i a zero one).eval X) =
          μ.expect (fun X => (if X i = false then g X else 0) * zero.eval X) +
          μ.expect (fun X => (if X i = true then g X else 0) * one.eval X) := by
        rw [← μ.expect_add]
        congr 1
        funext X
        cases h : X i <;> simp [DecisionTree.eval, h]
      rw [he]
      exact (abs_add_le _ _).trans (add_le_add (ih0 hT.1 _) (ih1 hT.2 _))

/-- A query whose answer is fixed on a cell selects just one child. -/
lemma simonPotential_query_indicator {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (i : I) (a : ℝ) (zero one : DecisionTree I)
    (C : Set (I → Bool)) (g : (I → Bool) → ℝ) (b : Bool)
    (hb : ∀ X ∈ C, X i = b) :
    simonPotential μ (.query i a zero one) (C.indicator g) =
      simonPotential μ (if b then one else zero) (C.indicator g) := by
  have hf (v : Bool) :
      (fun X => if X i = v then C.indicator g X else 0) =
        (if b = v then C.indicator g else fun _ => 0) := by
    funext X
    by_cases hX : X ∈ C
    · by_cases hv : b = v <;> simp [hv, Set.indicator_of_mem hX, hb X hX]
    · by_cases hv : b = v <;> simp [hv, Set.indicator_of_notMem hX]
  cases b <;> simp [simonPotential, hf]

private noncomputable def simonCentered (m : ℕ) (X : Fin (m * 2 ^ m) → Bool) : ℝ :=
  simonTarget m X - (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1))

private noncomputable def simonCellWeight (m : ℕ) (S : Finset (SimonGroup m))
    (z : SimonGroup m → SimonGroup m) : (Fin (m * 2 ^ m) → Bool) → ℝ :=
  (simonCell m S z).indicator (simonCentered m)

private noncomputable def simonCellMass (m : ℕ) (S : Finset (SimonGroup m))
    (z : SimonGroup m → SimonGroup m) : ℝ :=
  (simonLaw m).prob (· ∈ simonCell m S z)

private lemma simonCellMass_nonneg {m : ℕ} (S : Finset (SimonGroup m))
    (z : SimonGroup m → SimonGroup m) : 0 ≤ simonCellMass m S z :=
  (simonLaw m).prob_nonneg _

private lemma simonCentered_abs_le {m : ℕ} (hm : 2 ≤ m)
    (X : Fin (m * 2 ^ m) → Bool) : |simonCentered m X| ≤ 1 := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by
    exact_mod_cast (show 2 ≤ (2 : ℕ) ^ m from
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hr0 : 0 ≤ (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)) :=
    div_nonneg (by positivity) (by linarith)
  have hr1 : (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)) ≤ 1 := by
    apply (div_le_one (by linarith : (0 : ℝ) < 2 * (2 ^ m - 1))).mpr
    linarith
  unfold simonCentered
  rw [simonTarget_eq (by omega : 0 < m)]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

private lemma simonPotential_cell_le_mass {m : ℕ} (hm : 2 ≤ m)
    (T : DecisionTree (Fin (m * 2 ^ m))) (S : Finset (SimonGroup m))
    (z : SimonGroup m → SimonGroup m) :
    simonPotential (simonLaw m) T (simonCellWeight m S z) ≤ simonCellMass m S z := by
  apply (simonPotential_le_abs _ _ _).trans
  unfold FiniteLaw.expect simonCellMass FiniteLaw.prob
  apply Finset.sum_le_sum
  intro X _
  by_cases hX : X ∈ simonCell m S z
  · simpa [simonCellWeight, hX] using
      mul_le_of_le_one_right ((simonLaw m).nonneg X) (simonCentered_abs_le hm X)
  · simp [simonCellWeight, hX]

/-- Inserting a new argument partitions a cell according to its whole label. -/
private lemma simonCell_insert_iff {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} {x : SimonGroup m} (hx : x ∉ S)
    (w : SimonGroup m) (X : Fin (m * 2 ^ m) → Bool) :
    X ∈ simonCell m (insert x S) (Function.update z x w) ↔
      X ∈ simonCell m S z ∧ simonLabel m X x = w := by
  constructor
  · intro h
    refine ⟨?_, by simpa using h x (Finset.mem_insert_self _ _)⟩
    intro y hy
    have hyx : y ≠ x := by rintro rfl; exact hx hy
    simpa [Function.update_of_ne hyx] using h y (Finset.mem_insert_of_mem hy)
  · rintro ⟨h, hw⟩ y hy
    change y ∈ insert x S at hy
    rcases Finset.mem_insert.mp hy with he | hS
    · subst y
      simpa using hw
    · have hyx : y ≠ x := by intro he; exact hx (he ▸ hS)
      simpa [Function.update_of_ne hyx] using h y hS

private lemma simonCellWeight_insert {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} {x : SimonGroup m} (hx : x ∉ S)
    (w : SimonGroup m) (X : Fin (m * 2 ^ m) → Bool) :
    simonCellWeight m (insert x S) (Function.update z x w) X =
      if simonLabel m X x = w then simonCellWeight m S z X else 0 := by
  simp only [simonCellWeight, Set.indicator_apply, simonCell_insert_iff hx]
  by_cases hc : X ∈ simonCell m S z <;> by_cases hw : simonLabel m X x = w <;>
    simp [hc, hw]

private lemma simonCellWeight_partition {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} {x : SimonGroup m} (hx : x ∉ S) :
    (fun X => ∑ w : SimonGroup m,
      simonCellWeight m (insert x S) (Function.update z x w) X) = simonCellWeight m S z := by
  funext X
  simp [simonCellWeight_insert hx]

private lemma simonCellMass_partition {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} {x : SimonGroup m} (hx : x ∉ S)
    (W : Finset (SimonGroup m)) :
    ∑ w ∈ W, simonCellMass m (insert x S) (Function.update z x w) =
      (simonLaw m).prob (fun X => X ∈ simonCell m S z ∧ simonLabel m X x ∈ W) := by
  unfold simonCellMass FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  simp only [simonCell_insert_iff hx]
  by_cases hc : X ∈ simonCell m S z
  · simp [hc]
  · simp [hc]

private lemma simonCellMass_partition_univ {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} {x : SimonGroup m} (hx : x ∉ S) :
    ∑ w : SimonGroup m, simonCellMass m (insert x S) (Function.update z x w) =
      simonCellMass m S z := by
  rw [simonCellMass_partition hx]
  simp [simonCellMass]

private lemma simonCell_insert_injOn {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S)
    {x w : SimonGroup m} (hw : w ∉ S.image z) :
    Set.InjOn (Function.update z x w) (↑(insert x S) : Set (SimonGroup m)) := by
  intro a ha b hb he
  by_cases hax : a = x <;> by_cases hbx : b = x
  · exact hax.trans hbx.symm
  · subst a
    have hbS : b ∈ S := (Finset.mem_insert.mp hb).resolve_left hbx
    have he' : w = z b := by simpa [Function.update_of_ne hbx] using he
    exact (hw (Finset.mem_image.mpr ⟨b, hbS, he'.symm⟩)).elim
  · subst b
    have haS : a ∈ S := (Finset.mem_insert.mp ha).resolve_left hax
    have he' : z a = w := by simpa [Function.update_of_ne hax] using he
    exact (hw (Finset.mem_image.mpr ⟨a, haS, he'⟩)).elim
  · exact hz ((Finset.mem_insert.mp ha).resolve_left hax)
      ((Finset.mem_insert.mp hb).resolve_left hbx)
      (by simpa [Function.update_of_ne hax, Function.update_of_ne hbx] using he)

/-- The bit read at a coordinate is determined by the corresponding whole label. -/
private lemma simon_coord_bit {m : ℕ} (i : Fin (m * 2 ^ m))
    (X : Fin (m * 2 ^ m) → Bool) :
    X i = decide (simonLabel m X ((simonCoord m) i).2 ((simonCoord m) i).1 = 1) := by
  have hi : (simonCoord m).symm (((simonCoord m) i).1, ((simonCoord m) i).2) = i :=
    (simonCoord m).symm_apply_apply i
  simp only [simonLabel, hi]
  cases X i <;> simp

private lemma simon_collision_mass_le {m : ℕ} (hm : 2 ≤ m)
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m}
    {x : SimonGroup m} (hx : x ∉ S) :
    ∑ w ∈ S.image z, simonCellMass m (insert x S) (Function.update z x w) ≤
      (simonLaw m).prob (fun X => X ∈ simonCell m S z ∧
        simonMask m X ∈ S.image (x + ·)) := by
  rw [simonCellMass_partition hx]
  unfold FiniteLaw.prob
  apply Finset.sum_le_sum
  intro X _
  by_cases hs : X ∈ simonSupport m
  · have himp : X ∈ simonCell m S z ∧ simonLabel m X x ∈ S.image z →
        X ∈ simonCell m S z ∧ simonMask m X ∈ S.image (x + ·) := by
      rintro ⟨hc, hw⟩
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hw
      have hyx : y ≠ x := by rintro rfl; exact hx hy
      have hl : simonLabel m X x = simonLabel m X y := he.symm.trans (hc y hy).symm
      have heq := ((simonLabel_eq_iff hs x y).mp hl).resolve_left hyx
      have hsum : x + y = simonMask m X := by
        rw [heq, ← add_assoc]
        have hxx : x + x = 0 := by
          funext j
          change x j + x j = 0
          rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
        rw [hxx, zero_add]
      exact ⟨hc, Finset.mem_image.mpr ⟨y, hy, hsum⟩⟩
    by_cases hc : X ∈ simonCell m S z ∧ simonLabel m X x ∈ S.image z
    · simp [hc, himp hc]
    · simp only [hc, if_false]
      split_ifs <;> simp [(simonLaw m).nonneg]
  · simp [simonLaw_weight_of_not_mem hm hs]

private lemma hiding_choose_mono {a b : ℕ} (h : a ≤ b) :
    (a.choose 2 : ℝ) ≤ (b.choose 2 : ℝ) := by
  exact_mod_cast Nat.choose_le_choose 2 h

private lemma hiding_choose_succ (q : ℕ) :
    ((q + 1).choose 2 : ℝ) = (q.choose 2 : ℝ) + q := by
  rw [show (q + 1).choose 2 = q.choose 2 + q by
    simpa [Nat.add_comm] using Nat.choose_succ_succ q 1]
  push_cast
  rfl

/-- The leaf case, with a common denominator valid for the entire strategy. -/
private lemma simon_leaf_budget {m t r : ℕ} (hm : 2 ≤ m)
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m}
    (hz : Set.InjOn z S) (hqr : S.card ≤ r) (hrt : r ≤ t) :
    ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) *
        |(simonLaw m).expect (simonCellWeight m S z)| ≤
      simonCellMass m S z * (2 * (r.choose 2 : ℝ) - (S.card.choose 2 : ℝ)) := by
  have heq : ((simonDiffs S).card : ℝ) ≤ (S.card.choose 2 : ℝ) := by
    exact_mod_cast card_simonDiffs_le S
  have hqr' := hiding_choose_mono hqr
  have hrt' := hiding_choose_mono hrt
  have hm0 := simonCellMass_nonneg S z
  calc
    _ ≤ ((2 ^ m : ℝ) - 1 - (simonDiffs S).card) *
        |(simonLaw m).expect (simonCellWeight m S z)| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ ((simonDiffs S).card : ℝ) * simonCellMass m S z :=
      simon_cell_deviation_le hm hz
    _ ≤ simonCellMass m S z * (2 * (r.choose 2 : ℝ) - (S.card.choose 2 : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right (show ((simonDiffs S).card : ℝ) ≤
        2 * (r.choose 2 : ℝ) - (S.card.choose 2 : ℝ) by linarith) hm0]

private lemma simon_collision_budget {m t : ℕ} (hm : 2 ≤ m)
    (hct : (t.choose 2 : ℝ) < (2 ^ m : ℝ) - 1)
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m}
    (hz : Set.InjOn z S) {x : SimonGroup m} (hx : x ∉ S) (hqt : S.card ≤ t) :
    ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) *
        (∑ w ∈ S.image z, simonCellMass m (insert x S) (Function.update z x w)) ≤
      (S.card : ℝ) * simonCellMass m S z := by
  have he : ((simonDiffs S).card : ℝ) ≤ (t.choose 2 : ℝ) := by
    exact_mod_cast (card_simonDiffs_le S).trans (Nat.choose_le_choose 2 hqt)
  have hD : 0 ≤ (2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ) := by linarith
  calc
    _ ≤ ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) *
        (simonLaw m).prob (fun X => X ∈ simonCell m S z ∧
          simonMask m X ∈ S.image (x + ·)) :=
      mul_le_mul_of_nonneg_left (simon_collision_mass_le hm hx) hD
    _ ≤ ((2 ^ m : ℝ) - 1 - (simonDiffs S).card) *
        (simonLaw m).prob (fun X => X ∈ simonCell m S z ∧
          simonMask m X ∈ S.image (x + ·)) :=
      mul_le_mul_of_nonneg_right (by linarith) ((simonLaw m).prob_nonneg _)
    _ ≤ _ := by simpa [mul_comm, simonCellMass] using simon_collision_step_le hm hz x

private lemma simonPotential_query_cached {m : ℕ} (i : Fin (m * 2 ^ m)) (a : ℝ)
    (zero one : DecisionTree (Fin (m * 2 ^ m)))
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m}
    (hx : ((simonCoord m) i).2 ∈ S) :
    simonPotential (simonLaw m) (.query i a zero one) (simonCellWeight m S z) =
      simonPotential (simonLaw m)
        (if decide (z ((simonCoord m) i).2 ((simonCoord m) i).1 = 1) then one else zero)
        (simonCellWeight m S z) := by
  apply simonPotential_query_indicator
  intro X hX
  rw [simon_coord_bit i X, hX _ hx]

private lemma simonPotential_query_fresh {m : ℕ} (i : Fin (m * 2 ^ m)) (a : ℝ)
    (zero one : DecisionTree (Fin (m * 2 ^ m)))
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m}
    (hx : ((simonCoord m) i).2 ∉ S) :
    simonPotential (simonLaw m) (.query i a zero one) (simonCellWeight m S z) ≤
      ∑ w : SimonGroup m, simonPotential (simonLaw m)
        (if decide (w ((simonCoord m) i).1 = 1) then one else zero)
        (simonCellWeight m (insert ((simonCoord m) i).2 S)
          (Function.update z ((simonCoord m) i).2 w)) := by
  calc
    _ = simonPotential (simonLaw m) (.query i a zero one)
        (fun X => ∑ w : SimonGroup m,
          simonCellWeight m (insert ((simonCoord m) i).2 S)
            (Function.update z ((simonCoord m) i).2 w) X) := by
      rw [simonCellWeight_partition hx]
    _ ≤ ∑ w : SimonGroup m, simonPotential (simonLaw m) (.query i a zero one)
        (simonCellWeight m (insert ((simonCoord m) i).2 S)
          (Function.update z ((simonCoord m) i).2 w)) := simonPotential_sum_le _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      apply simonPotential_query_indicator
      intro X hX
      rw [simon_coord_bit i X,
        (simonCell_insert_iff hx w X).mp hX |>.2]

/-- Sum fresh-label continuation bounds and the crude bounds on colliding labels. -/
private lemma hiding_sum_good_bad {A : Type*} [Fintype A]
    (bad : Finset A) (mass value : A → ℝ) (D B : ℝ)
    (hmass : ∀ a, 0 ≤ mass a) (hB : 0 ≤ B)
    (hgood : ∀ a ∉ bad, D * value a ≤ mass a * B)
    (hbad : ∀ a ∈ bad, D * value a ≤ D * mass a) :
    D * ∑ a, value a ≤ (∑ a, mass a) * B + D * ∑ a ∈ bad, mass a := by
  have hs : (∑ a, if a ∈ bad then mass a else 0) = ∑ a ∈ bad, mass a := by
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ a, D * value a := Finset.mul_sum _ _ _
    _ ≤ ∑ a, (mass a * B + D * (if a ∈ bad then mass a else 0)) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a ∈ bad
      · simp only [ha, if_true]
        exact (hbad a ha).trans (le_add_of_nonneg_left (mul_nonneg (hmass a) hB))
      · simpa [ha] using hgood a ha
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hs]

/-- Adaptive invariant. Here `r = |S| + d`; using `depth ≤ d` permits either
child of an unbalanced tree and also permits cached queries. The denominator is fixed
at the global depth budget `t`. -/
private lemma simonPotential_invariant {m t : ℕ} (hm : 2 ≤ m)
    (hct : (t.choose 2 : ℝ) < (2 ^ m : ℝ) - 1)
    (T : DecisionTree (Fin (m * 2 ^ m)))
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m}
    (hz : Set.InjOn z S) {r : ℕ} (hqr : S.card + T.depth ≤ r) (hrt : r ≤ t) :
    ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) *
        simonPotential (simonLaw m) T (simonCellWeight m S z) ≤
      simonCellMass m S z * (2 * (r.choose 2 : ℝ) - (S.card.choose 2 : ℝ)) := by
  have hD : 0 ≤ (2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ) := by linarith
  induction T generalizing S z r with
  | leaf a =>
      exact simon_leaf_budget hm hz (by simpa [DecisionTree.depth] using hqr) hrt
  | query i a zero one ih0 ih1 =>
      have hd : S.card + (1 + max zero.depth one.depth) ≤ r := hqr
      have hd0 : S.card + zero.depth ≤ r := by omega
      have hd1 : S.card + one.depth ≤ r := by omega
      by_cases hx : ((simonCoord m) i).2 ∈ S
      · rw [simonPotential_query_cached i a zero one hx]
        split_ifs
        · exact ih1 hz hd1 hrt
        · exact ih0 hz hd0 hrt
      · let x := ((simonCoord m) i).2
        let j := ((simonCoord m) i).1
        let branch (w : SimonGroup m) := if decide (w j = 1) then one else zero
        let mass (w : SimonGroup m) :=
          simonCellMass m (insert x S) (Function.update z x w)
        let value (w : SimonGroup m) := simonPotential (simonLaw m) (branch w)
          (simonCellWeight m (insert x S) (Function.update z x w))
        let B : ℝ := 2 * (r.choose 2 : ℝ) - ((S.card + 1).choose 2 : ℝ)
        have hq1r : S.card + 1 ≤ r := by omega
        have hB : 0 ≤ B := by
          have hc := hiding_choose_mono hq1r
          have hn : (0 : ℝ) ≤ (r.choose 2 : ℝ) := by positivity
          dsimp [B]
          linarith
        have hmass : ∀ w, 0 ≤ mass w := fun w => simonCellMass_nonneg _ _
        have hgood (w : SimonGroup m) (hw : w ∉ S.image z) :
            ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) * value w ≤ mass w * B := by
          have hzinj := simonCell_insert_injOn hz hw (x := x)
          have hi0 : (insert x S).card + zero.depth ≤ r := by
            rw [Finset.card_insert_of_notMem hx]
            omega
          have hi1 : (insert x S).card + one.depth ≤ r := by
            rw [Finset.card_insert_of_notMem hx]
            omega
          have hi : ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) *
              simonPotential (simonLaw m) (branch w)
                (simonCellWeight m (insert x S) (Function.update z x w)) ≤
              mass w * (2 * (r.choose 2 : ℝ) - ((insert x S).card.choose 2 : ℝ)) := by
            dsimp [branch, mass]
            split_ifs
            · exact ih1 hzinj hi1 hrt
            · exact ih0 hzinj hi0 hrt
          simpa only [value, B, Finset.card_insert_of_notMem (show x ∉ S from hx)] using hi
        have hbad (w : SimonGroup m) (_hw : w ∈ S.image z) :
            ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) * value w ≤
              ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) * mass w :=
          mul_le_mul_of_nonneg_left (simonPotential_cell_le_mass hm (branch w) _ _) hD
        have hsum := hiding_sum_good_bad (S.image z) mass value
          ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) B hmass hB hgood hbad
        have htotal : ∑ w, mass w = simonCellMass m S z := simonCellMass_partition_univ hx
        rw [htotal] at hsum
        calc
          _ ≤ ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) * ∑ w, value w :=
            mul_le_mul_of_nonneg_left (simonPotential_query_fresh i a zero one hx) hD
          _ ≤ simonCellMass m S z * B +
              ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) * ∑ w ∈ S.image z, mass w := hsum
          _ ≤ simonCellMass m S z * B + (S.card : ℝ) * simonCellMass m S z :=
            by
            have hcoll := simon_collision_budget hm hct hz hx (by omega : S.card ≤ t)
            exact add_le_add le_rfl hcoll
          _ = _ := by
            dsimp [B]
            rw [hiding_choose_succ]
            ring

private lemma simonPotential_bound {m : ℕ} (hm : 2 ≤ m) {t : ℕ}
    (hct : (t.choose 2 : ℝ) < (2 ^ m : ℝ) - 1)
    (T : DecisionTree (Fin (m * 2 ^ m))) (hT : T.depth ≤ t) :
    simonPotential (simonLaw m) T (simonCentered m) ≤
      2 * (t.choose 2 : ℝ) / ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ)) := by
  have hz : Set.InjOn (fun _ : SimonGroup m => (0 : SimonGroup m))
      (↑(∅ : Finset (SimonGroup m)) : Set (SimonGroup m)) := by simp [Set.InjOn]
  have hi := simonPotential_invariant hm hct T hz (r := t) (by simpa using hT) le_rfl
  have hc : simonCell m ∅ (fun _ => (0 : SimonGroup m)) = Set.univ := by
    ext X
    simp [simonCell]
  have hw : simonCellWeight m ∅ (fun _ => (0 : SimonGroup m)) = simonCentered m := by
    simp [simonCellWeight, hc]
  have hm1 : simonCellMass m ∅ (fun _ => (0 : SimonGroup m)) = 1 := by
    simp [simonCellMass, hc, FiniteLaw.prob, (simonLaw m).total]
  rw [hw, hm1] at hi
  simp only [Finset.card_empty, Nat.choose_zero_succ, Nat.cast_zero, sub_zero, one_mul] at hi
  apply (le_div_iff₀ (by linarith : 0 < (2 ^ m : ℝ) - 1 - (t.choose 2 : ℝ))).mpr
  simpa only [mul_comm] using hi

/-- (30.1) in bit-transcript form (Lemma `ian:simon-adaptive-posterior` with Corollary
`ian:simon-bit-hiding`): for every tree of depth at most `t`,
`Σ_τ |E_μ[(Y - ρ_m) 1{leafPath = τ}]| ≤ 2c_t/(N - c_t)`. -/
theorem simon_transcript_bound {m : ℕ} (hm : 2 ≤ m) {t : ℕ}
    (hct : ((t.choose 2 : ℕ) : ℝ) < (2 ^ m : ℝ) - 1)
    (T : DecisionTree (Fin (m * 2 ^ m))) (hT : T.depth ≤ t) :
    ∑ p ∈ Finset.univ.image (fun X => leafPath T X),
        |(simonLaw m).expect (fun X => if leafPath T X = p then
          simonTarget m X - (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)) else 0)| ≤
      2 * ((t.choose 2 : ℕ) : ℝ) / ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℕ)) := by
  simpa only [simonPotential_eq_transcripts, simonCentered] using
    simonPotential_bound hm hct T hT

/-- Corollary `ian:simon-bit-hiding`: `sup_{F ∈ \mathcal F_t} |Cov_μ(Y, F)| ≤ η_t`. -/
theorem simon_cov_signTree_le {m : ℕ} (hm : 2 ≤ m) {t : ℕ}
    (hct : ((t.choose 2 : ℕ) : ℝ) < (2 ^ m : ℝ) - 1)
    {F : DecisionTree (Fin (m * 2 ^ m))} (hF : F ∈ SignTrees (Fin (m * 2 ^ m)) t) :
    |cov (simonLaw m) (simonTarget m) F.eval| ≤
      2 * ((t.choose 2 : ℕ) : ℝ) / ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℕ)) := by
  rw [← expect_centered_mul_eq_cov, simonLaw_expect_target hm]
  exact (simonPotential_eval_le (simonLaw m) F hF.2 (simonCentered m)).trans
    (simonPotential_bound hm hct F hF.1)

/-- Corollary `ian:simon-bit-hiding`: `sup_{D ∈ \mathcal D_t} |Cov_μ(Y, D)| ≤ η_t / 2`. -/
theorem simon_cov_depthTree_le {m : ℕ} (hm : 2 ≤ m) {t : ℕ}
    (hct : ((t.choose 2 : ℕ) : ℝ) < (2 ^ m : ℝ) - 1)
    {D : DecisionTree (Fin (m * 2 ^ m))} (hD : D ∈ DepthTrees (Fin (m * 2 ^ m)) t) :
    |cov (simonLaw m) (simonTarget m) D.eval| ≤
      2 * ((t.choose 2 : ℕ) : ℝ) / ((2 ^ m : ℝ) - 1 - (t.choose 2 : ℕ)) / 2 := by
  apply (covCondition_iff (simonTarget m) (simonLaw m) t _).mp _ D hD
  intro F hF
  rw [expect_centered_mul_eq_cov]
  exact simon_cov_signTree_le hm hct hF

end UnifiedAA.HardSector
