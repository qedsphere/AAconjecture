import UnifiedAA.DecisionTree
import UnifiedAA.ProbabilityBounds
import Mathlib.Data.Fintype.Pi

/-!
# Hard sectors: basic definitions (HS1.1)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, the opening paragraph,
Definition `ian:hard-sector-definition`, and the paragraph after it.

Oracle inputs are `I → Bool` (the notes' `Ω_n = {-1,1}^n`, relabelled); laws on inputs are
`FiniteLaw (I → Bool)`. Trees are `UnifiedAA.DecisionTree`; only leaf outputs matter for
evaluation, the `summary` field of query nodes is ignored.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- Every leaf output of the tree satisfies `P` (the `summary` of query nodes is ignored). -/
def LeavesIn {I : Type*} (P : ℝ → Prop) : DecisionTree I → Prop
  | .leaf a => P a
  | .query _ _ zero one => LeavesIn P zero ∧ LeavesIn P one

/-- `\mathcal D_t` in `13_hard_sector_definitions_forward.tex`: deterministic coordinate
decision trees of worst-case depth at most `t` with leaf outputs in `[0,1]`. -/
def DepthTrees (I : Type*) (t : ℕ) : Set (DecisionTree I) :=
  {D | D.depth ≤ t ∧ LeavesIn (fun v => 0 ≤ v ∧ v ≤ 1) D}

/-- `\mathcal F_t` in `13_hard_sector_definitions_forward.tex`: deterministic coordinate
decision trees of worst-case depth at most `t` with leaf outputs in `[-1,1]`. -/
def SignTrees (I : Type*) (t : ℕ) : Set (DecisionTree I) :=
  {F | F.depth ≤ t ∧ LeavesIn (fun v => -1 ≤ v ∧ v ≤ 1) F}

/-- Covariance `Cov_ν(f,g)` under a finite law. -/
def cov {A : Type*} [Fintype A] (ν : FiniteLaw A) (f g : A → ℝ) : ℝ :=
  ν.expect (fun x => (f x - ν.expect f) * (g x - ν.expect g))

/-- The conditional law `μ(· | H)`, defined when `μ(H) > 0`. -/
noncomputable def condLaw {A : Type*} [Fintype A] (μ : FiniteLaw A) (H : Set A)
    (hH : 0 < μ.prob (· ∈ H)) : FiniteLaw A := by
  classical
  exact
    { weight := fun x => (if x ∈ H then μ.weight x else 0) / μ.prob (· ∈ H)
      nonneg := fun x => div_nonneg (by split_ifs <;> simp [μ.nonneg]) hH.le
      total := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        change μ.prob (· ∈ H) / μ.prob (· ∈ H) = 1
        exact div_self (ne_of_gt hH) }

/-- The covariance condition of `Hard` (Definition `ian:hard-sector-definition`):
`|E_ν[(Q - m_ν) F]| ≤ γ` for every `F ∈ \mathcal F_t`, where `m_ν = E_ν Q`. -/
def CovCondition {I : Type*} [Fintype I] [DecidableEq I] (Q : (I → Bool) → ℝ)
    (ν : FiniteLaw (I → Bool)) (t : ℕ) (γ : ℝ) : Prop :=
  ∀ F ∈ SignTrees I t, |ν.expect (fun x => (Q x - ν.expect Q) * F.eval x)| ≤ γ

/-- `Hard(Q,ν;t,a,γ)` (Definition `ian:hard-sector-definition`): `Var_ν Q ≥ a` and the
covariance condition at depth `t`. The definition is stated for `0 < γ < a ≤ 1/4`; that
parameter range is part of the assertion here. -/
def Hard {I : Type*} [Fintype I] [DecidableEq I] (Q : (I → Bool) → ℝ)
    (ν : FiniteLaw (I → Bool)) (t : ℕ) (a γ : ℝ) : Prop :=
  0 < γ ∧ γ < a ∧ a ≤ 1 / 4 ∧ a ≤ ν.variance Q ∧ CovCondition Q ν t γ

/-- Smooth sector of weight `w ∈ (0,1]` (Definition `ian:hard-sector-definition`): a law `ν`
with `Hard(Q,ν;t,a,γ)` and `w ν(x) ≤ μ(x)` for all `x`. -/
def IsSmoothSector {I : Type*} [Fintype I] [DecidableEq I] (μ ν : FiniteLaw (I → Bool))
    (Q : (I → Bool) → ℝ) (t : ℕ) (a γ w : ℝ) : Prop :=
  0 < w ∧ w ≤ 1 ∧ (∀ x, w * ν.weight x ≤ μ.weight x) ∧ Hard Q ν t a γ

/-- Set sector of weight `w ∈ (0,1]` (Definition `ian:hard-sector-definition`): a set `H` with
`μ(H) ≥ w` whose conditional law `μ(· | H)` satisfies `Hard(Q,μ(·|H);t,a,γ)`. -/
def IsSetSector {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    (H : Set (I → Bool)) (Q : (I → Bool) → ℝ) (t : ℕ) (a γ w : ℝ) : Prop :=
  0 < w ∧ w ≤ 1 ∧ w ≤ μ.prob (· ∈ H) ∧
    ∃ hH : 0 < μ.prob (· ∈ H), Hard Q (condLaw μ H hH) t a γ
-- LOCK END

/-- Apply a function to leaf answers while preserving queries and their summaries. -/
def mapLeaves {I : Type*} (φ : ℝ → ℝ) : DecisionTree I → DecisionTree I
  | .leaf v => .leaf (φ v)
  | .query i a zero one => .query i a (mapLeaves φ zero) (mapLeaves φ one)

@[simp] theorem eval_mapLeaves {I : Type*} (φ : ℝ → ℝ) (T : DecisionTree I)
    (x : I → Bool) : (mapLeaves φ T).eval x = φ (T.eval x) := by
  induction T with
  | leaf v => rfl
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [mapLeaves, DecisionTree.eval, hx, ih0, ih1]

@[simp] theorem depth_mapLeaves {I : Type*} (φ : ℝ → ℝ) (T : DecisionTree I) :
    (mapLeaves φ T).depth = T.depth := by
  induction T with
  | leaf v => rfl
  | query i a zero one ih0 ih1 => simp [mapLeaves, DecisionTree.depth, ih0, ih1]

theorem leavesIn_mapLeaves {I : Type*} {P P' : ℝ → Prop} (φ : ℝ → ℝ)
    (T : DecisionTree I) (hT : LeavesIn P T) (hφ : ∀ v, P v → P' (φ v)) :
    LeavesIn P' (mapLeaves φ T) := by
  induction T with
  | leaf v => exact hφ v hT
  | query i a zero one ih0 ih1 => exact ⟨ih0 hT.1, ih1 hT.2⟩

/-- Opening paragraph of `13_hard_sector_definitions_forward.tex`:
`\mathcal D_t ⊆ \mathcal D_{t'}` for `t ≤ t'`. -/
theorem depthTrees_mono {I : Type*} {t t' : ℕ} (htt' : t ≤ t') :
    DepthTrees I t ⊆ DepthTrees I t' := by
  intro D hD
  exact ⟨hD.1.trans htt', hD.2⟩

/-- Opening paragraph of `13_hard_sector_definitions_forward.tex`:
`\mathcal F_t ⊆ \mathcal F_{t'}` for `t ≤ t'`. -/
theorem signTrees_mono {I : Type*} {t t' : ℕ} (htt' : t ≤ t') :
    SignTrees I t ⊆ SignTrees I t' := by
  intro F hF
  exact ⟨hF.1.trans htt', hF.2⟩

/-- Paragraph after `ian:hard-sector-definition`, `\mathcal F_t ⊆ \{2D-1 : D ∈ \mathcal D_t\}`
as functions on inputs. -/
theorem exists_depthTree_of_signTree {I : Type*} {t : ℕ} {F : DecisionTree I}
    (hF : F ∈ SignTrees I t) :
    ∃ D ∈ DepthTrees I t, ∀ x, F.eval x = 2 * D.eval x - 1 := by
  refine ⟨mapLeaves (fun v => (v + 1) / 2) F, ⟨?_, ?_⟩, ?_⟩
  · simpa only [depth_mapLeaves] using hF.1
  · exact leavesIn_mapLeaves _ F hF.2 (fun v hv => by
      constructor <;> linarith [hv.1, hv.2])
  · intro x
    rw [eval_mapLeaves]
    ring

/-- Paragraph after `ian:hard-sector-definition`, `\{2D-1 : D ∈ \mathcal D_t\} ⊆ \mathcal F_t`
as functions on inputs. -/
theorem exists_signTree_of_depthTree {I : Type*} {t : ℕ} {D : DecisionTree I}
    (hD : D ∈ DepthTrees I t) :
    ∃ F ∈ SignTrees I t, ∀ x, F.eval x = 2 * D.eval x - 1 := by
  refine ⟨mapLeaves (fun v => 2 * v - 1) D, ⟨?_, ?_⟩, ?_⟩
  · simpa only [depth_mapLeaves] using hD.1
  · exact leavesIn_mapLeaves _ D hD.2 (fun v hv => by
      constructor <;> linarith [hv.1, hv.2])
  · intro x
    exact eval_mapLeaves _ D x

/-- Paragraph after `ian:hard-sector-definition`: since `E_ν(f - m_ν) = 0`,
`E_ν[(f - m_ν) g] = Cov_ν(f,g)`. -/
theorem expect_centered_mul_eq_cov {A : Type*} [Fintype A] (ν : FiniteLaw A)
    (f g : A → ℝ) :
    ν.expect (fun x => (f x - ν.expect f) * g x) = cov ν f g := by
  have hpoint : (fun x => (f x - ν.expect f) * (g x - ν.expect g)) =
      (fun x => (f x - ν.expect f) * g x +
        (-ν.expect g) * (f x - ν.expect f)) := by
    funext x
    ring
  rw [cov, hpoint, ν.expect_add, ν.expect_const_mul, ν.expect_sub_mean,
    mul_zero, add_zero]

/-- The affine conversion of leaf answers doubles their centered correlation. -/
theorem expect_centered_mul_two_sub_one {A : Type*} [Fintype A] (ν : FiniteLaw A)
    (f g : A → ℝ) :
    ν.expect (fun x => (f x - ν.expect f) * (2 * g x - 1)) = 2 * cov ν f g := by
  have hpoint : (fun x => (f x - ν.expect f) * (2 * g x - 1)) =
      (fun x => 2 * ((f x - ν.expect f) * g x) + (-1) * (f x - ν.expect f)) := by
    funext x
    ring
  rw [hpoint, ν.expect_add, ν.expect_const_mul, ν.expect_const_mul,
    ν.expect_sub_mean, mul_zero, add_zero, expect_centered_mul_eq_cov]

/-- Paragraph after `ian:hard-sector-definition`: the covariance condition of `Hard` says
exactly `|Cov_ν(Q,D)| ≤ γ/2` for every `D ∈ \mathcal D_t`. -/
theorem covCondition_iff {I : Type*} [Fintype I] [DecidableEq I] (Q : (I → Bool) → ℝ)
    (ν : FiniteLaw (I → Bool)) (t : ℕ) (γ : ℝ) :
    CovCondition Q ν t γ ↔ ∀ D ∈ DepthTrees I t, |cov ν Q D.eval| ≤ γ / 2 := by
  constructor
  · intro h D hD
    obtain ⟨F, hF, heval⟩ := exists_signTree_of_depthTree hD
    have hbound := h F hF
    simp_rw [heval] at hbound
    rw [expect_centered_mul_two_sub_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      at hbound
    linarith
  · intro h F hF
    obtain ⟨D, hD, heval⟩ := exists_depthTree_of_signTree hF
    have hbound := h D hD
    simp_rw [heval]
    rw [expect_centered_mul_two_sub_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-- Paragraph after `ian:hard-sector-definition`: `Hard(Q,ν;t',a,γ)` implies
`Hard(Q,ν;t,a,γ)` for `t ≤ t'`. -/
theorem hard_of_le {I : Type*} [Fintype I] [DecidableEq I] {Q : (I → Bool) → ℝ}
    {ν : FiniteLaw (I → Bool)} {t t' : ℕ} {a γ : ℝ} (htt' : t ≤ t')
    (h : Hard Q ν t' a γ) : Hard Q ν t a γ := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun F hF => h.2.2.2.2 F (signTrees_mono htt' hF)⟩

/-- Definition `ian:hard-sector-definition`: `μ(· | H) ≤ μ / μ(H)` pointwise. -/
theorem condLaw_weight_le {A : Type*} [Fintype A] (μ : FiniteLaw A) (H : Set A)
    (hH : 0 < μ.prob (· ∈ H)) (x : A) :
    (condLaw μ H hH).weight x ≤ μ.weight x / μ.prob (· ∈ H) := by
  classical
  change (if x ∈ H then μ.weight x else 0) / μ.prob (· ∈ H) ≤ _
  apply div_le_div_of_nonneg_right _ hH.le
  split_ifs <;> simp [μ.nonneg]

/-- Definition `ian:hard-sector-definition`: every set sector of weight `w` is a smooth sector
of the same weight, namely `ν = μ(· | H)`. -/
theorem isSmoothSector_of_isSetSector {I : Type*} [Fintype I] [DecidableEq I]
    {μ : FiniteLaw (I → Bool)} {H : Set (I → Bool)} {Q : (I → Bool) → ℝ} {t : ℕ}
    {a γ w : ℝ} (hS : IsSetSector μ H Q t a γ w) (hH : 0 < μ.prob (· ∈ H)) :
    IsSmoothSector μ (condLaw μ H hH) Q t a γ w := by
  obtain ⟨hw, hw1, hmass, hhard⟩ := hS
  obtain ⟨_, hhard⟩ := hhard
  refine ⟨hw, hw1, ?_, hhard⟩
  intro x
  calc
    w * (condLaw μ H hH).weight x ≤
        w * (μ.weight x / μ.prob (· ∈ H)) :=
      mul_le_mul_of_nonneg_left (condLaw_weight_le μ H hH x) hw.le
    _ ≤ μ.prob (· ∈ H) * (μ.weight x / μ.prob (· ∈ H)) :=
      mul_le_mul_of_nonneg_right hmass (div_nonneg (μ.nonneg x) hH.le)
    _ = μ.weight x := mul_div_cancel₀ _ (ne_of_gt hH)

end UnifiedAA.HardSector
