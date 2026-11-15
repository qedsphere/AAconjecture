import UnifiedAA.HardSector.Optimal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hard sectors: one calibrated predictor (HS1.6)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, Theorem
`ian:hard-sector-regularity` and its proof (lines 58-107).

For `Q ∈ [0,1]`, `t ≥ 1`, `0 < γ < a ≤ 1/4`, `0 < w ≤ 1`, `M = ⌈1/γ⌉` and every `K ≥ 1`: either
there is a set sector `H` of weight `w` with `Hard(Q, μ(·|H); t, a, γ)`, with `H = g⁻¹(I)` for an
interval `I` and a tree `g` of depth at most `k t`, `k < K`; or
`ℓ_μ(Kt, Q) ≤ √a + (M w + 1/(K γ²))/2`, stated as "some `D ∈ \mathcal D_{Kt}` has
`E_μ|D - Q| ≤ …`". The intervals are `[lo, hi)` or `[lo, hi]` (the bins of the proof are
half-open except the last).
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

/-- Cauchy–Schwarz for a finite law, used twice in the proof of Theorem
`ian:hard-sector-regularity`: `(E[fg])^2 ≤ E[f^2] E[g^2]`. -/
theorem expect_mul_sq_le {A : Type*} [Fintype A] (μ : FiniteLaw A) (f g : A → ℝ) :
    (μ.expect (fun x => f x * g x)) ^ 2 ≤
      μ.expect (fun x => f x ^ 2) * μ.expect (fun x => g x ^ 2) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg (f x)))
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg (g x)))
    (fun x _ => by dsimp; nlinarith [sq_nonneg (μ.weight x * f x * g x)])

/-- Proof of Theorem `ian:hard-sector-regularity`: for `Y ∈ [0,1]` and `m = E Y`,
`E|Y - m| ≤ 2m(1 - m) ≤ 1/2`. -/
theorem expect_abs_sub_mean_le_half {A : Type*} [Fintype A] (μ : FiniteLaw A) (f : A → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    μ.expect (fun x => |f x - μ.expect f|) ≤ 1 / 2 := by
  have hm0 : 0 ≤ μ.expect f := by
    simpa only [μ.expect_const] using μ.expect_mono (fun x => (hf x).1)
  have hm1 : μ.expect f ≤ 1 := by
    simpa only [μ.expect_const] using μ.expect_mono (fun x => (hf x).2)
  have hp : ∀ x, |f x - μ.expect f| ≤
      f x * (1 - μ.expect f) + (1 - f x) * μ.expect f := by
    intro x
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg (hf x).1 (sub_nonneg.mpr hm1),
      mul_nonneg (sub_nonneg.mpr (hf x).2) hm0]
  have he : (fun x => f x * (1 - μ.expect f) + (1 - f x) * μ.expect f) =
      (fun x => (1 - 2 * μ.expect f) * f x + μ.expect f) := by
    funext x; ring
  have h := μ.expect_mono hp
  rw [he, μ.expect_add, μ.expect_const_mul, μ.expect_const] at h
  nlinarith [sq_nonneg (μ.expect f - 1 / 2)]

/-- Proof of Theorem `ian:hard-sector-regularity`: by Cauchy–Schwarz,
`E|Y - m| ≤ √(Var Y)`. -/
theorem expect_abs_sub_mean_le_sqrt_variance {A : Type*} [Fintype A] (μ : FiniteLaw A)
    (f : A → ℝ) :
    μ.expect (fun x => |f x - μ.expect f|) ≤ Real.sqrt (μ.variance f) := by
  have h := expect_mul_sq_le μ (fun x => |f x - μ.expect f|) (fun _ => 1)
  simp only [mul_one, one_pow, μ.expect_const, sq_abs] at h
  have hs := Real.sq_sqrt (μ.variance_nonneg f)
  have hn := Real.sqrt_nonneg (μ.variance f)
  change (μ.expect (fun x => |f x - μ.expect f|)) ^ 2 ≤ μ.variance f at h
  nlinarith

/-- An expectation restricted to one cell of a finite partition. -/
noncomputable def partExpect {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) (f : A → ℝ) : ℝ := by
  classical
  exact μ.expect (fun x => if b x = j then f x else 0)

noncomputable abbrev partMass {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) : ℝ := μ.prob (fun x => b x = j)

/-- Null cells use the original law; all formulas multiply them by their zero mass. -/
noncomputable def partLaw {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) : FiniteLaw A :=
  if h : 0 < partMass μ b j then condLaw μ {x | b x = j} h else μ

lemma partMass_nonneg {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) : 0 ≤ partMass μ b j := μ.prob_nonneg _

lemma weight_le_partMass {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (x : A) : μ.weight x ≤ partMass μ b (b x) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => if b y = b x then μ.weight y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (Finset.mem_univ x)
  simpa [partMass, FiniteLaw.prob] using h

lemma partExpect_eq_zero {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) (hj : partMass μ b j = 0) (f : A → ℝ) :
    partExpect μ b j f = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : b x = j
  · have hw : μ.weight x = 0 := le_antisymm
      (by simpa [hx, hj] using weight_le_partMass μ b x) (μ.nonneg x)
    simp [hw]
  · simp [hx]

lemma partExpect_eq {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) (f : A → ℝ) :
    partExpect μ b j f = partMass μ b j * (partLaw μ b j).expect f := by
  classical
  by_cases hj : 0 < partMass μ b j
  · rw [partLaw, dif_pos hj, expect_condLaw]
    have he : ({x | b x = j}.indicator f) = (fun x => if b x = j then f x else 0) := by
      funext x; simp [Set.indicator]
    rw [he]
    exact (mul_div_cancel₀ _ (ne_of_gt hj)).symm
  · have hz := le_antisymm (le_of_not_gt hj) (partMass_nonneg μ b j)
    rw [partExpect_eq_zero μ b j hz, hz, zero_mul]

lemma expect_partition {A J : Type*} [Fintype A] [Fintype J] (μ : FiniteLaw A)
    (b : A → J) (f : A → ℝ) :
    μ.expect f = ∑ j, partMass μ b j * (partLaw μ b j).expect f := by
  classical
  simp_rw [← partExpect_eq, partExpect, FiniteLaw.expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_ite, mul_zero]
  simp

lemma partMass_sum {A J : Type*} [Fintype A] [Fintype J] (μ : FiniteLaw A)
    (b : A → J) : ∑ j, partMass μ b j = 1 := by
  simpa only [μ.expect_const, FiniteLaw.expect_const, mul_one] using
    (expect_partition μ b (fun _ => 1)).symm

lemma partLaw_mono {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) (hj : 0 < partMass μ b j) {f g : A → ℝ}
    (hfg : ∀ x, b x = j → f x ≤ g x) :
    (partLaw μ b j).expect f ≤ (partLaw μ b j).expect g := by
  classical
  rw [partLaw, dif_pos hj, expect_condLaw, expect_condLaw]
  apply div_le_div_of_nonneg_right _ hj.le
  apply μ.expect_mono
  intro x
  by_cases hx : b x = j
  · simpa [Set.indicator, hx] using hfg x hx
  · simp [Set.indicator, hx]

lemma partLaw_congr {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) (hj : 0 < partMass μ b j) {f g : A → ℝ}
    (hfg : ∀ x, b x = j → f x = g x) :
    (partLaw μ b j).expect f = (partLaw μ b j).expect g :=
  le_antisymm (partLaw_mono μ b j hj (fun x hx => (hfg x hx).le))
    (partLaw_mono μ b j hj (fun x hx => (hfg x hx).ge))

lemma expect_nonneg' {A : Type*} [Fintype A] (μ : FiniteLaw A) {f : A → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by
  simpa only [μ.expect_const] using μ.expect_mono hf

lemma expect_sub' {A : Type*} [Fintype A] (μ : FiniteLaw A) (f g : A → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  have he : (fun x => f x - g x) = (fun x => f x + (-1) * g x) := by
    funext x; ring
  rw [he, μ.expect_add, μ.expect_const_mul]
  ring

lemma expect_mean_mem {A : Type*} [Fintype A] (μ : FiniteLaw A) {f : A → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ μ.expect f ∧ μ.expect f ≤ 1 := by
  exact ⟨expect_nonneg' μ (fun x => (hf x).1),
    by simpa only [μ.expect_const] using μ.expect_mono (fun x => (hf x).2)⟩

/-- A narrow predictor has small covariance with any bounded sign test. -/
lemma cov_le_of_narrow {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (b : A → J) (j : J) (hj : 0 < partMass μ b j) (g F : A → ℝ)
    (hF : ∀ x, -1 ≤ F x ∧ F x ≤ 1) (c r : ℝ) (hr : 0 ≤ r)
    (hg : ∀ x, b x = j → |g x - c| ≤ r) :
    |cov (partLaw μ b j) g F| ≤ r := by
  let ν := partLaw μ b j
  have hg2 : ν.variance g ≤ r ^ 2 := by
    have hm := partLaw_mono μ b j hj (fun x hx =>
      (sq_le_sq₀ (abs_nonneg _) hr).mpr (hg x hx))
    simp only [sq_abs, FiniteLaw.expect_const] at hm
    rw [ν.mse_eq_variance_add_sq] at hm
    nlinarith [sq_nonneg (ν.expect g - c)]
  have hF2 : ν.variance F ≤ 1 := by
    have hm := ν.expect_mono (fun x => show (F x - 0) ^ 2 ≤ (1 : ℝ) by
      obtain ⟨h0, h1⟩ := hF x
      nlinarith)
    rw [ν.expect_const, ν.mse_eq_variance_add_sq] at hm
    nlinarith [sq_nonneg (ν.expect F - 0)]
  have hcs := expect_mul_sq_le ν (fun x => g x - ν.expect g)
    (fun x => F x - ν.expect F)
  change (cov ν g F) ^ 2 ≤ ν.variance g * ν.variance F at hcs
  have hn := ν.variance_nonneg g
  have hh : (cov ν g F) ^ 2 ≤ r ^ 2 := by nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) hr).mp (by simpa only [sq_abs] using hh)

/-- Pigeonhole principle for the squared-loss budget. -/
lemma exists_small_drop (R : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (h0 : R 0 ≤ 1 / 4) (hKn : 0 ≤ R K) :
    ∃ k < K, R k - R (k + 1) ≤ 1 / (4 * K) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  by_contra! h
  have hsum : ∑ k ∈ Finset.range K, (R k - R (k + 1)) = R 0 - R K := by
    clear hK hKn hKpos h
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ, ih]; ring
  have hh : ∑ _k ∈ Finset.range K, (1 / (4 * (K : ℝ))) <
      ∑ k ∈ Finset.range K, (R k - R (k + 1)) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨0, Finset.mem_range.mpr hK⟩
    · intro k hk; exact h k (Finset.mem_range.mp hk)
  rw [hsum] at hh
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  have he : (K : ℝ) * (1 / (4 * K)) = 1 / 4 := by field_simp
  rw [he] at hh
  linarith

/-- The equal-width bin index, with the endpoint `1` in the last bin. -/
noncomputable def regBin (M : ℕ) (hM : 0 < M) (v : ℝ) : Fin M :=
  ⟨min ⌊v * M⌋₊ (M - 1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

lemma regBin_eq_iff (M : ℕ) (hM : 0 < M) (v : ℝ)
    (hv : 0 ≤ v ∧ v ≤ 1) (j : Fin M) :
    regBin M hM v = j ↔
      (j.val : ℝ) / M ≤ v ∧
        (if j.val = M - 1 then v ≤ 1 else v < (j.val + 1 : ℝ) / M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hm1 : (M - 1 : ℕ) + 1 = M := by omega
  have hcast : ((M - 1 : ℕ) : ℝ) + 1 = M := by exact_mod_cast hm1
  have hfloor := Nat.floor_le (mul_nonneg hv.1 hMr.le)
  have hupper := Nat.lt_floor_add_one (v * M)
  rw [Fin.ext_iff]
  change min ⌊v * M⌋₊ (M - 1) = j.val ↔ _
  by_cases hj : j.val = M - 1
  · simp only [hj, if_true, min_eq_right_iff]
    rw [Nat.le_floor_iff (mul_nonneg hv.1 hMr.le), div_le_iff₀ hMr]
    exact ⟨fun h => ⟨h, hv.2⟩, fun h => h.1⟩
  · have hjlt : j.val < M - 1 := by omega
    simp only [hj, if_false, div_le_iff₀ hMr, lt_div_iff₀ hMr]
    constructor
    · intro he
      have he' : ⌊v * M⌋₊ = j.val := by omega
      rw [he'] at hfloor hupper
      exact ⟨hfloor, hupper⟩
    · rintro ⟨hl, hu⟩
      have hl' : j.val ≤ ⌊v * M⌋₊ := Nat.le_floor hl
      have hu' : ⌊v * M⌋₊ < j.val + 1 := by
        apply (Nat.floor_lt (mul_nonneg hv.1 hMr.le)).mpr
        exact_mod_cast hu
      omega

lemma regBin_narrow (M : ℕ) (hM : 0 < M) (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1)
    (j : Fin M) (hj : regBin M hM v = j) :
    |v - ((j.val : ℝ) + 1 / 2) / M| ≤ 1 / (2 * M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hl, hu⟩ := (regBin_eq_iff M hM v hv j).mp hj
  have hu' : v ≤ (j.val + 1 : ℝ) / M := by
    split_ifs at hu with hjlast
    · have he : (j.val : ℝ) + 1 = M := by exact_mod_cast (show j.val + 1 = M by omega)
      simpa [he, ne_of_gt hMr] using hu
    · exact hu.le
  apply abs_le.mpr
  constructor <;> field_simp at * <;> nlinarith

lemma regBin_cell_interval {A : Type*} (M : ℕ) (hM : 0 < M)
    (g : A → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (j : Fin M) :
    ∃ lo hi : ℝ,
      {x | regBin M hM (g x) = j} = g ⁻¹' Set.Ico lo hi ∨
      {x | regBin M hM (g x) = j} = g ⁻¹' Set.Icc lo hi := by
  by_cases hj : j.val = M - 1
  · refine ⟨j.val / M, 1, Or.inr ?_⟩
    ext x
    simpa [hj] using regBin_eq_iff M hM (g x) (hg x) j
  · refine ⟨j.val / M, (j.val + 1 : ℝ) / M, Or.inl ?_⟩
    ext x
    simpa [hj] using regBin_eq_iff M hM (g x) (hg x) j

lemma reciprocal_ceil_bounds {γ : ℝ} (hγ : 0 < γ) :
    0 < ⌈1 / γ⌉₊ ∧ 1 / (2 * (⌈1 / γ⌉₊ : ℝ)) ≤ γ / 2 := by
  have hM := Nat.ceil_pos.mpr (one_div_pos.mpr hγ)
  have hMr : (0 : ℝ) < ⌈1 / γ⌉₊ := by exact_mod_cast hM
  have hceil := Nat.le_ceil (1 / γ)
  have hmul : 1 ≤ (⌈1 / γ⌉₊ : ℝ) * γ := (div_le_iff₀ hγ).mp hceil
  exact ⟨hM, (div_le_iff₀ (by positivity)).mpr (by nlinarith)⟩

/-- Choose an optimal calibrated tree at a scale with a small next-scale improvement. -/
lemma exists_optimal_small_drop {I : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) {Q : (I → Bool) → ℝ}
    (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) (t K : ℕ) (hK : 1 ≤ K) :
    ∃ k < K, ∃ T : DecisionTree I, T.depth ≤ k * t ∧
      ∀ D ∈ DepthTrees I ((k + 1) * t),
        sqLoss μ Q (condMeanTree μ Q T) - sqLoss μ Q D ≤ 1 / (4 * K) := by
  classical
  choose T hdepth hmin using (fun j => exists_sqLoss_min μ Q (j * t))
  let R := fun j => sqLoss μ Q (condMeanTree μ Q (T j))
  have h0 : R 0 ≤ 1 / 4 := by
    have hleaf : (DecisionTree.leaf (1 / 2) : DecisionTree I) ∈ DepthTrees I (0 * t) :=
      ⟨by simp [DecisionTree.depth], by norm_num [LeavesIn]⟩
    have hh := hmin 0 _ hleaf
    have hb := μ.expect_mono (fun x => show (Q x - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) by
      obtain ⟨h0, h1⟩ := hQ x; nlinarith)
    rw [μ.expect_const] at hb
    exact hh.trans hb
  have hKn : 0 ≤ R K := expect_nonneg' μ (fun x => sq_nonneg _)
  obtain ⟨k, hk, hdrop⟩ := exists_small_drop R K hK h0 hKn
  exact ⟨k, hk, T k, hdepth k, fun D hD => by
    have hh := hmin (k + 1) D hD
    dsimp [R] at hdrop
    linarith⟩

lemma exists_positive_test {I : Type*} [Fintype I] [DecidableEq I]
    (ν : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (t : ℕ) (γ : ℝ)
    (hn : ¬ CovCondition Q ν t γ) :
    ∃ F ∈ SignTrees I t, γ < cov ν Q F.eval := by
  classical
  simp only [CovCondition, not_forall, not_le] at hn
  obtain ⟨F, hF, hh⟩ := hn
  rw [expect_centered_mul_eq_cov] at hh
  rcases lt_abs.mp hh with hh | hh
  · exact ⟨F, hF, hh⟩
  · refine ⟨mapLeaves (fun v => -v) F, ⟨?_, ?_⟩, ?_⟩
    · simpa only [depth_mapLeaves] using hF.1
    · exact leavesIn_mapLeaves _ _ hF.2 (fun v hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩)
    · rw [← expect_centered_mul_eq_cov]
      have he : (fun x => (Q x - ν.expect Q) * (mapLeaves (fun v => -v) F).eval x) =
          (fun x => (-1) * ((Q x - ν.expect Q) * F.eval x)) := by
        funext x; rw [eval_mapLeaves]; ring
      rw [he, ν.expect_const_mul, expect_centered_mul_eq_cov]
      linarith

/-- Calibration passes from leaves to any finite grouping of the leaf answers. -/
lemma part_residual_zero {I J : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (T : DecisionTree I)
    (β : ℝ → J) (j : J)
    (hj : 0 < partMass μ (fun x => β ((condMeanTree μ Q T).eval x)) j) :
    (partLaw μ (fun x => β ((condMeanTree μ Q T).eval x)) j).expect
      (fun x => Q x - (condMeanTree μ Q T).eval x) = 0 := by
  classical
  have hz := expect_resid_mul_eq_zero μ Q T
    (fun p => if β (cellMean μ Q (leafPath T) p) = j then 1 else 0)
  have he : (fun x => (Q x - (condMeanTree μ Q T).eval x) *
      (if β (cellMean μ Q (leafPath T) (leafPath T x)) = j then 1 else 0)) =
      (fun x => if β ((condMeanTree μ Q T).eval x) = j then
        Q x - (condMeanTree μ Q T).eval x else 0) := by
    funext x
    rw [eval_condMeanTree]
    split_ifs <;> ring
  rw [he] at hz
  change partExpect μ _ j _ = 0 at hz
  rw [partExpect_eq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hj)

lemma exists_residual_test {I J : Type*} [Fintype I] [DecidableEq I]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (g : (I → Bool) → ℝ)
    (b : (I → Bool) → J) (j : J) (hj : 0 < partMass μ b j)
    (t : ℕ) (γ : ℝ) (hγ : 0 < γ) (c : ℝ)
    (hnarrow : ∀ x, b x = j → |g x - c| ≤ γ / 2)
    (hcal : (partLaw μ b j).expect (fun x => Q x - g x) = 0)
    (hbad : ¬ CovCondition Q (partLaw μ b j) t γ) :
    ∃ F ∈ SignTrees I t,
      γ / 2 < (partLaw μ b j).expect (fun x => (Q x - g x) * F.eval x) := by
  let ν := partLaw μ b j
  obtain ⟨F, hF, hh⟩ := exists_positive_test ν Q t γ hbad
  have hc := cov_le_of_narrow μ b j hj g F.eval
    (eval_mem_of_leavesIn hF.2) c (γ / 2) (by positivity) hnarrow
  have hm : ν.expect Q = ν.expect g := by
    rw [expect_sub'] at hcal
    linarith
  have he : (fun x => (Q x - g x) * F.eval x) =
      (fun x => (Q x - ν.expect Q) * F.eval x -
        (g x - ν.expect g) * F.eval x) := by
    funext x; rw [hm]; ring
  refine ⟨F, hF, ?_⟩
  rw [he, expect_sub', expect_centered_mul_eq_cov, expect_centered_mul_eq_cov]
  linarith [(abs_le.mp hc).2]

/-- The total mass of tests with residual correlation `γ/2` is paid for by the
squared-loss improvement of one grafting step. -/
lemma bad_mass_bound {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ)
    (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) (g : DecisionTree I) (s t K : ℕ)
    (hg : g ∈ DepthTrees I s) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ)
    (hdrop : ∀ D ∈ DepthTrees I (s + t), sqLoss μ Q g - sqLoss μ Q D ≤ 1 / (4 * K))
    (β : ℝ → J) (B : J → Prop) [DecidablePred B] (F : J → DecisionTree I)
    (hF : ∀ j, B j → F j ∈ SignTrees I t)
    (hcor : ∀ j, B j →
      γ / 2 ≤ (partLaw μ (fun x => β (g.eval x)) j).expect
        (fun x => (Q x - g.eval x) * (F j).eval x)) :
    (∑ j, if B j then partMass μ (fun x => β (g.eval x)) j else 0) ≤
      1 / (K * γ ^ 2) := by
  classical
  let b := fun x => β (g.eval x)
  let p : ℝ := ∑ j, if B j then partMass μ b j else 0
  let C : List Bool → ℝ → DecisionTree I :=
    fun _ v => if B (β v) then F (β v) else .leaf 0
  let S := graft g C
  let Z := S.eval
  have hC : ∀ q v, (C q v).depth ≤ t ∧ LeavesIn (fun v => -1 ≤ v ∧ v ≤ 1) (C q v) := by
    intro q v
    dsimp [C]
    split_ifs with h
    · exact hF _ h
    · exact ⟨Nat.zero_le _, by norm_num [LeavesIn]⟩
  have hS := graft_depth_le_and_leavesIn g C hg.1 hC
  have hZ : ∀ x, Z x = if B (b x) then (F (b x)).eval x else 0 := by
    intro x
    dsimp [Z, S]
    rw [eval_graft]
    dsimp [C, b]
    split_ifs <;> rfl
  have hp : 0 ≤ p := Finset.sum_nonneg (fun j _ => by
    split_ifs; exact partMass_nonneg μ b j; exact le_rfl)
  have hz2 : μ.expect (fun x => Z x ^ 2) ≤ p := by
    have hh : ∀ x, Z x ^ 2 ≤ if B (b x) then (1 : ℝ) else 0 := by
      intro x
      rw [hZ]
      split_ifs with hb
      · obtain ⟨hl, hu⟩ := eval_mem_of_leavesIn (hF _ hb).2 x
        nlinarith
      · norm_num
    have he : μ.expect (fun x => if B (b x) then (1 : ℝ) else 0) = p := by
      rw [expect_partition μ b]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : 0 < partMass μ b j
      · rw [partLaw_congr μ b j hj (g := fun _ => if B j then 1 else 0)
          (fun x hx => by rw [hx]), FiniteLaw.expect_const]
        split_ifs <;> simp
      · have hz := le_antisymm (le_of_not_gt hj) (partMass_nonneg μ b j)
        simp [hz]
    exact (μ.expect_mono hh).trans_eq he
  have hcorr : p * γ / 2 ≤ μ.expect (fun x => (Q x - g.eval x) * Z x) := by
    rw [expect_partition μ b]
    dsimp [p]
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : 0 < partMass μ b j
    · have he := partLaw_congr μ b j hj
        (f := fun x => (Q x - g.eval x) * Z x)
        (g := fun x => if B j then (Q x - g.eval x) * (F j).eval x else 0)
        (fun x hx => by rw [hZ x, hx]; split_ifs <;> simp)
      rw [he]
      by_cases hb : B j
      · simp only [hb, if_true]
        have hh := mul_le_mul_of_nonneg_left (hcor j hb) (partMass_nonneg μ b j)
        nlinarith
      · simp [hb, FiniteLaw.expect_const]
    · have hz := le_antisymm (le_of_not_gt hj) (partMass_nonneg μ b j)
      simp [hz]
  let g' := condMeanTree μ Q S
  have hg' : g' ∈ DepthTrees I (s + t) := condMeanTree_mem_depthTrees μ hQ hS.1
  obtain ⟨f, hf⟩ := exists_eval_eq_comp_leafPath g
  obtain ⟨f', hf'⟩ := exists_factor_leafPath_graft g C f
  have hpy := sq_pythagoras μ Q S f'
  have hfac : ∀ x, f' (leafPath S x) = g.eval x := fun x => (hf' x).symm.trans (hf x).symm
  simp_rw [hfac] at hpy
  change sqLoss μ Q g = sqLoss μ Q g' + μ.expect (fun x => (g'.eval x - g.eval x) ^ 2) at hpy
  have hbudget : μ.expect (fun x => (g'.eval x - g.eval x) ^ 2) ≤ 1 / (4 * K) := by
    have hh := hdrop g' hg'
    linarith
  obtain ⟨z, hz⟩ := exists_eval_eq_comp_leafPath S
  have hcal := expect_resid_mul_eq_zero μ Q S z
  simp_rw [← hz] at hcal
  have he : (fun x => (Q x - g.eval x) * Z x) =
      (fun x => (g'.eval x - g.eval x) * Z x + (Q x - g'.eval x) * Z x) := by
    funext x; ring
  rw [he, μ.expect_add] at hcorr
  change μ.expect (fun x => (Q x - g'.eval x) * Z x) = 0 at hcal
  rw [hcal, add_zero] at hcorr
  have hcs := expect_mul_sq_le μ (fun x => g'.eval x - g.eval x) Z
  have hupper : (μ.expect (fun x => (g'.eval x - g.eval x) * Z x)) ^ 2 ≤
      (1 / (4 * K)) * p := by
    exact hcs.trans (mul_le_mul hbudget hz2
      (expect_nonneg' μ (fun x => sq_nonneg _)) (by positivity))
  have hsq : (p * γ / 2) ^ 2 ≤ (1 / (4 * K)) * p := by
    have hn : 0 ≤ p * γ / 2 := by positivity
    nlinarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hmul : p * (K * γ ^ 2) ≤ 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have he : (1 / (4 * (K : ℝ))) * p = p / (4 * K) := by ring
      rw [he] at hsq
      have hh : (p * γ / 2) ^ 2 * (4 * K) ≤ p :=
        (le_div_iff₀ (by positivity)).mp hsq
      apply (mul_le_mul_iff_right₀ hp').mp
      nlinarith
  exact (le_div_iff₀ (by positivity)).mpr (by simpa [p, b] using hmul)

/-- Output the conditional mean in each bin and sum its absolute-loss bounds. -/
lemma exists_partition_predictor {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ)
    (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) (g : DecisionTree I) (s : ℕ)
    (hg : g ∈ DepthTrees I s) (β : ℝ → J) (B : J → Prop) [DecidablePred B]
    (a w : ℝ) (hw : 0 ≤ w)
    (hlarge : ∀ j, a ≤ (partLaw μ (fun x => β (g.eval x)) j).variance Q →
      partMass μ (fun x => β (g.eval x)) j ≤ w ∨ B j) :
    ∃ D ∈ DepthTrees I s,
      l1Loss μ Q D ≤ Real.sqrt a +
        ((Fintype.card J : ℝ) * w +
          ∑ j, if B j then partMass μ (fun x => β (g.eval x)) j else 0) / 2 := by
  classical
  let b := fun x => β (g.eval x)
  let m := fun j => (partLaw μ b j).expect Q
  let φ := fun v => m (β v)
  let D := mapLeaves φ g
  have hD : D ∈ DepthTrees I s := ⟨by simpa [D] using hg.1,
    leavesIn_mapLeaves φ g hg.2 (fun v _ => expect_mean_mem _ hQ)⟩
  have hcell : ∀ j,
      partMass μ b j * (partLaw μ b j).expect (fun x => |D.eval x - Q x|) ≤
        partMass μ b j * Real.sqrt a + (w + (if B j then partMass μ b j else 0)) / 2 := by
    intro j
    have hp := partMass_nonneg μ b j
    by_cases hj : 0 < partMass μ b j
    · have he := partLaw_congr μ b j hj
        (f := fun x => |D.eval x - Q x|) (g := fun x => |Q x - m j|)
        (fun x hx => by
          simp only [D, eval_mapLeaves]
          change |m (b x) - Q x| = _
          rw [hx, abs_sub_comm])
      rw [he]
      by_cases hv : (partLaw μ b j).variance Q < a
      · have hh := (expect_abs_sub_mean_le_sqrt_variance (partLaw μ b j) Q).trans
          (Real.sqrt_le_sqrt hv.le)
        have hh' := mul_le_mul_of_nonneg_left hh hp
        have hb : 0 ≤ (if B j then partMass μ b j else 0) := by
          split_ifs <;> positivity
        dsimp [m]
        linarith
      · have hh := mul_le_mul_of_nonneg_left
          (expect_abs_sub_mean_le_half (partLaw μ b j) Q hQ) hp
        have hs := mul_nonneg hp (Real.sqrt_nonneg a)
        rcases hlarge j (le_of_not_gt hv) with hl | hb
        · have hb' : 0 ≤ (if B j then partMass μ b j else 0) := by
            split_ifs <;> positivity
          dsimp [m]
          linarith
        · simp only [hb, if_true]
          dsimp [m]
          linarith
    · have hz := le_antisymm (le_of_not_gt hj) hp
      simp only [hz, zero_mul, ite_self, add_zero]
      positivity
  refine ⟨D, hD, ?_⟩
  unfold l1Loss
  rw [expect_partition μ b]
  calc
    _ ≤ ∑ j, (partMass μ b j * Real.sqrt a +
        (w + (if B j then partMass μ b j else 0)) / 2) :=
      Finset.sum_le_sum (fun j _ => hcell j)
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, nsmul_eq_mul, partMass_sum]
      dsimp [b]
      ring

/-- Theorem `ian:hard-sector-regularity` (one calibrated predictor). -/
theorem regularity {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    {Q : (I → Bool) → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    {a γ w : ℝ} (hγ : 0 < γ) (hγa : γ < a) (ha : a ≤ 1 / 4) (hw : 0 < w) (hw1 : w ≤ 1)
    (K : ℕ) (hK : 1 ≤ K) :
    (∃ H : Set (I → Bool), IsSetSector μ H Q t a γ w ∧
        ∃ k < K, ∃ g ∈ DepthTrees I (k * t), ∃ lo hi : ℝ,
          H = g.eval ⁻¹' Set.Ico lo hi ∨ H = g.eval ⁻¹' Set.Icc lo hi) ∨
      ∃ D ∈ DepthTrees I (K * t),
        l1Loss μ Q D ≤ Real.sqrt a + ((⌈1 / γ⌉₊ : ℝ) * w + 1 / (K * γ ^ 2)) / 2 := by
  classical
  obtain ⟨k, hk, T, hT, hdrop⟩ := exists_optimal_small_drop μ hQ t K hK
  let g := condMeanTree μ Q T
  have hg : g ∈ DepthTrees I (k * t) := condMeanTree_mem_depthTrees μ hQ hT
  let M := ⌈1 / γ⌉₊
  have hM : 0 < M := (reciprocal_ceil_bounds hγ).1
  let β := regBin M hM
  let b := fun x => β (g.eval x)
  by_cases hex : ∃ j : Fin M, w ≤ partMass μ b j ∧
      a ≤ (partLaw μ b j).variance Q ∧ CovCondition Q (partLaw μ b j) t γ
  · obtain ⟨j, hjw, hjv, hjc⟩ := hex
    have hj : 0 < partMass μ b j := hw.trans_le hjw
    have he : partLaw μ b j = condLaw μ {x | b x = j} hj := by
      rw [partLaw, dif_pos hj]
    refine Or.inl ⟨{x | b x = j}, ⟨hw, hw1, hjw, hj, ?_⟩,
      k, hk, g, hg, ?_⟩
    · rw [← he]
      exact ⟨hγ, hγa, ha, hjv, hjc⟩
    · exact regBin_cell_interval M hM g.eval (eval_mem_of_leavesIn hg.2) j
  · let B := fun j : Fin M => 0 < partMass μ b j ∧ ¬ CovCondition Q (partLaw μ b j) t γ
    have htests : ∀ j : Fin M, ∃ F ∈ SignTrees I t, B j →
        γ / 2 ≤ (partLaw μ b j).expect (fun x => (Q x - g.eval x) * F.eval x) := by
      intro j
      by_cases hj : B j
      · obtain ⟨F, hF, hcorr⟩ := exists_residual_test μ Q g.eval b j hj.1 t γ hγ
          (((j.val : ℝ) + 1 / 2) / M)
          (fun x hx => (regBin_narrow M hM (g.eval x)
            (eval_mem_of_leavesIn hg.2 x) j hx).trans (reciprocal_ceil_bounds hγ).2)
          (part_residual_zero μ Q T β j hj.1) hj.2
        exact ⟨F, hF, fun _ => hcorr.le⟩
      · exact ⟨.leaf 0, ⟨Nat.zero_le _, by norm_num [LeavesIn]⟩, fun h => (hj h).elim⟩
    choose F hF hcorr using htests
    have hp := bad_mass_bound μ Q hQ g (k * t) t K hg hK γ hγ
      (fun D hD => hdrop D (by simpa only [Nat.add_mul, Nat.one_mul] using hD))
      β B F (fun j _ => hF j) hcorr
    have hlarge : ∀ j : Fin M, a ≤ (partLaw μ b j).variance Q →
        partMass μ b j ≤ w ∨ B j := by
      intro j hjv
      by_cases hjw : partMass μ b j ≤ w
      · exact Or.inl hjw
      · have hjw' : w < partMass μ b j := lt_of_not_ge hjw
        refine Or.inr ⟨hw.trans hjw', ?_⟩
        intro hjc
        exact hex ⟨j, hjw'.le, hjv, hjc⟩
    obtain ⟨D, hD, hLoss⟩ := exists_partition_predictor μ Q hQ g (k * t) hg β B a w hw.le hlarge
    refine Or.inr ⟨D, depthTrees_mono (Nat.mul_le_mul_right t hk.le) hD, ?_⟩
    simp only [Fintype.card_fin] at hLoss
    change (∑ j, if B j then partMass μ b j else 0) ≤ 1 / (K * γ ^ 2) at hp
    change l1Loss μ Q D ≤ Real.sqrt a + ((M : ℝ) * w + _) / 2 at hLoss
    dsimp only [M] at hLoss
    linarith

/-- Theorem `ian:hard-sector-regularity`, last sentence: with `K = ⌈1/(wγ²)⌉`, the second
alternative gives `ℓ_μ(Kt, Q) ≤ √a + M w`. -/
theorem regularity_of_K_eq {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    {Q : (I → Bool) → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    {a γ w : ℝ} (hγ : 0 < γ) (hγa : γ < a) (ha : a ≤ 1 / 4) (hw : 0 < w) (hw1 : w ≤ 1) :
    (∃ H : Set (I → Bool), IsSetSector μ H Q t a γ w ∧
        ∃ k < ⌈1 / (w * γ ^ 2)⌉₊, ∃ g ∈ DepthTrees I (k * t), ∃ lo hi : ℝ,
          H = g.eval ⁻¹' Set.Ico lo hi ∨ H = g.eval ⁻¹' Set.Icc lo hi) ∨
      ∃ D ∈ DepthTrees I (⌈1 / (w * γ ^ 2)⌉₊ * t),
        l1Loss μ Q D ≤ Real.sqrt a + (⌈1 / γ⌉₊ : ℝ) * w := by
  classical
  let K := ⌈1 / (w * γ ^ 2)⌉₊
  have hpos : 0 < w * γ ^ 2 := mul_pos hw (sq_pos_of_pos hγ)
  have hK : 1 ≤ K := Nat.ceil_pos.mpr (one_div_pos.mpr hpos)
  rcases regularity μ hQ ht hγ hγa ha hw hw1 K hK with h | ⟨D, hD, hLoss⟩
  · exact Or.inl h
  · refine Or.inr ⟨D, hD, ?_⟩
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hceil : 1 ≤ (K : ℝ) * (w * γ ^ 2) :=
      (div_le_iff₀ hpos).mp (Nat.le_ceil (1 / (w * γ ^ 2)))
    have hrec : 1 / ((K : ℝ) * γ ^ 2) ≤ w :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have hM : (1 : ℝ) ≤ ⌈1 / γ⌉₊ := by
      exact_mod_cast (reciprocal_ceil_bounds hγ).1
    have hwM : w ≤ (⌈1 / γ⌉₊ : ℝ) * w := by nlinarith
    linarith

#print axioms expect_mul_sq_le
#print axioms expect_abs_sub_mean_le_half
#print axioms expect_abs_sub_mean_le_sqrt_variance
#print axioms regularity
#print axioms regularity_of_K_eq

end UnifiedAA.HardSector
