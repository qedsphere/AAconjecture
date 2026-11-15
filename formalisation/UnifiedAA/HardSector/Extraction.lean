import UnifiedAA.HardSector.Regularity

/-!
# Hard sectors: explicit polynomial smooth and set extraction (HS1.7)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, Corollary
`ian:hard-sector-explicit` and its proof (lines 115-141).

For `Q ∈ [0,1]`, `t ≥ 1`, `0 < ε < 1/8`, `0 < η ≤ 1/4`, with
`L† = ⌈32 ε^{-5} η^{-2}⌉ t` and `L* = ⌈256 ε^{-7} η^{-3}⌉ t`: if `ℓ_μ(L†, Q) > ε` (in particular
if `ℓ_μ(L*, Q) > ε`), there is `H` with membership decided by a tree of depth below `L†`, with
`μ(H) ≥ ηε³/16` and `Hard(Q, μ(·|H); t, ε²/4, ηε²/4)`; `μ(·|H)` is then a smooth sector of
weight `ηε³/16`. "Membership decided by a tree `D`" means `D` has leaf outputs in `{0,1}` and
`x ∈ H ↔ D x = 1`.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

/-- Turn any set of leaf answers into a Boolean membership decision tree. -/
lemma exists_membership_tree {I : Type*} (g : DecisionTree I) (S : Set ℝ) :
    ∃ D : DecisionTree I, D.depth = g.depth ∧
      LeavesIn (fun v => v = 0 ∨ v = 1) D ∧
      ∀ x, x ∈ g.eval ⁻¹' S ↔ D.eval x = 1 := by
  classical
  refine ⟨mapLeaves (fun v => if v ∈ S then 1 else 0) g, depth_mapLeaves _ _, ?_, ?_⟩
  · have h : LeavesIn (fun _ => True) g := by
      induction g with
      | leaf v => trivial
      | query i a z o ihz iho => exact ⟨ihz, iho⟩
    exact leavesIn_mapLeaves _ _ h (fun v _ => by split_ifs <;> simp)
  · intro x
    simp only [Set.mem_preimage, eval_mapLeaves]
    split_ifs <;> simp_all

/-- Corollary `ian:hard-sector-explicit`, main form: from `ℓ_μ(L†, Q) > ε`. -/
theorem extraction {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    {Q : (I → Bool) → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    {ε η : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hell : ε < ell μ (⌈32 / (ε ^ 5 * η ^ 2)⌉₊ * t) Q) :
    ∃ H : Set (I → Bool),
      IsSetSector μ H Q t (ε ^ 2 / 4) (η * ε ^ 2 / 4) (η * ε ^ 3 / 16) ∧
      ∃ D : DecisionTree I, D.depth < ⌈32 / (ε ^ 5 * η ^ 2)⌉₊ * t ∧
        LeavesIn (fun v => v = 0 ∨ v = 1) D ∧ ∀ x, x ∈ H ↔ D.eval x = 1 := by
  classical
  let a := ε ^ 2 / 4
  let γ := η * ε ^ 2 / 4
  let M := ⌈1 / γ⌉₊
  let w := ε / (2 * (M : ℝ))
  let K := ⌈32 / (ε ^ 5 * η ^ 2)⌉₊
  have hε1 : ε ≤ 1 := by linarith
  have hη1 : η < 1 := by linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha : a ≤ 1 / 4 := by dsimp [a]; nlinarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγa : γ < a := by
    change η * ε ^ 2 / 4 < ε ^ 2 / 4
    nlinarith [mul_pos (sub_pos.mpr hη1) (sq_pos_of_pos hε)]
  have hγ1 : γ ≤ 1 := by linarith
  have hM : 0 < M := Nat.ceil_pos.mpr (one_div_pos.mpr hγ)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hMγ : (M : ℝ) * γ ≤ 2 := by
    have hc : (M : ℝ) ≤ 1 / γ + 1 :=
      (Nat.ceil_lt_add_one (le_of_lt (one_div_pos.mpr hγ))).le
    have hm : (1 : ℝ) ≤ 1 / γ := (le_div_iff₀ hγ).mpr (by simpa using hγ1)
    have hc' : (M : ℝ) ≤ 2 / γ := by
      calc
        (M : ℝ) ≤ 1 / γ + 1 := hc
        _ ≤ 1 / γ + 1 / γ := add_le_add le_rfl hm
        _ = 2 / γ := by ring
    exact (le_div_iff₀ hγ).mp hc'
  have hweight : η * ε ^ 3 / 16 ≤ w := by
    have he : η * ε ^ 3 / 16 = ε * γ / 4 := by dsimp [γ]; ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
    calc
      ε * γ / 4 * (2 * (M : ℝ)) = (ε / 2) * ((M : ℝ) * γ) := by ring
      _ ≤ (ε / 2) * 2 := mul_le_mul_of_nonneg_left hMγ (by positivity)
      _ = ε := by ring
  have hK : 1 ≤ K := Nat.ceil_pos.mpr (by positivity)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hratio : 2 / (ε * γ ^ 2) = 32 / (ε ^ 5 * η ^ 2) := by
    dsimp [γ]
    field_simp
    ring
  have hceil : 2 / (ε * γ ^ 2) ≤ (K : ℝ) := by
    rw [hratio]
    exact Nat.le_ceil _
  have hrec : 1 / ((K : ℝ) * γ ^ 2) ≤ ε / 2 := by
    have hc := (div_le_iff₀ (by positivity : 0 < ε * γ ^ 2)).mp hceil
    apply (div_le_iff₀ (by positivity : 0 < (K : ℝ) * γ ^ 2)).mpr
    nlinarith
  have hsqrt : Real.sqrt a = ε / 2 := by
    have he : a = (ε / 2) ^ 2 := by dsimp [a]; ring
    rw [he, Real.sqrt_sq (by positivity)]
  have hMw : (M : ℝ) * w = ε / 2 := by
    dsimp [w]
    field_simp
  rcases regularity μ hQ ht hγ hγa ha hw hw1 K hK with hsector | ⟨D, hD, hloss⟩
  · obtain ⟨H, hH, k, hk, g, hg, lo, hi, hinterval⟩ := hsector
    refine ⟨H, ⟨by positivity, hweight.trans hw1, hweight.trans hH.2.2.1,
      hH.2.2.2⟩, ?_⟩
    have hd : g.depth < K * t :=
      hg.1.trans_lt (Nat.mul_lt_mul_of_pos_right hk (by omega))
    rcases hinterval with hinterval | hinterval
    · obtain ⟨D, hdD, hleaves, heval⟩ := exists_membership_tree g (Set.Ico lo hi)
      exact ⟨D, hdD.trans_lt hd, hleaves, by simpa only [hinterval] using heval⟩
    · obtain ⟨D, hdD, hleaves, heval⟩ := exists_membership_tree g (Set.Icc lo hi)
      exact ⟨D, hdD.trans_lt hd, hleaves, by simpa only [hinterval] using heval⟩
  · have hellD := (ell_attained μ Q (K * t)).2 D hD
    rw [hsqrt, hMw] at hloss
    have he : ell μ (K * t) Q ≤ ε := by linarith
    exact False.elim ((not_lt_of_ge he) hell)

/-- Corollary `ian:hard-sector-explicit`, "in particular": `L† ≤ L*`, so `ℓ_μ(L*, Q) > ε`
gives the same conclusion. -/
theorem extraction_of_Lstar {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    {Q : (I → Bool) → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    {ε η : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hell : ε < ell μ (⌈256 / (ε ^ 7 * η ^ 3)⌉₊ * t) Q) :
    ∃ H : Set (I → Bool),
      IsSetSector μ H Q t (ε ^ 2 / 4) (η * ε ^ 2 / 4) (η * ε ^ 3 / 16) ∧
      ∃ D : DecisionTree I, D.depth < ⌈32 / (ε ^ 5 * η ^ 2)⌉₊ * t ∧
        LeavesIn (fun v => v = 0 ∨ v = 1) D ∧ ∀ x, x ∈ H ↔ D.eval x = 1 := by
  have hε1 : ε ≤ 1 := by linarith
  have hη1 : η ≤ 1 := by linarith
  have hs : ε ^ 2 ≤ 1 := by nlinarith
  have hp : ε ^ 2 * η ≤ 1 :=
    (mul_le_mul_of_nonneg_right hs hη.le).trans (by simpa using hη1)
  have hratio : 32 / (ε ^ 5 * η ^ 2) ≤ 256 / (ε ^ 7 * η ^ 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      32 * (ε ^ 7 * η ^ 3) = (32 * (ε ^ 2 * η)) * (ε ^ 5 * η ^ 2) := by ring
      _ ≤ 256 * (ε ^ 5 * η ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hdepth := Nat.mul_le_mul_right t (Nat.ceil_mono hratio)
  exact extraction μ hQ ht hε hε8 hη hη4
    (hell.trans_le (ell_antitone μ Q hdepth))

/-- Corollary `ian:hard-sector-explicit`, last sentence: `ν = μ(·|H) ≤ 16μ/(ηε³)` is a smooth
sector of weight `ηε³/16`. -/
theorem extraction_smooth {I : Type*} [Fintype I] [DecidableEq I] (μ : FiniteLaw (I → Bool))
    {Q : (I → Bool) → ℝ} (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    {ε η : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hell : ε < ell μ (⌈32 / (ε ^ 5 * η ^ 2)⌉₊ * t) Q) :
    ∃ H : Set (I → Bool), ∃ hH : 0 < μ.prob (· ∈ H),
      (∀ x, (condLaw μ H hH).weight x ≤ 16 / (η * ε ^ 3) * μ.weight x) ∧
      IsSmoothSector μ (condLaw μ H hH) Q t (ε ^ 2 / 4) (η * ε ^ 2 / 4) (η * ε ^ 3 / 16) := by
  obtain ⟨H, hS, _⟩ := extraction μ hQ ht hε hε8 hη hη4 hell
  have hH : 0 < μ.prob (· ∈ H) := hS.1.trans_le hS.2.2.1
  refine ⟨H, hH, ?_, isSmoothSector_of_isSetSector hS hH⟩
  intro x
  calc
    (condLaw μ H hH).weight x ≤ μ.weight x / μ.prob (· ∈ H) :=
      condLaw_weight_le μ H hH x
    _ ≤ μ.weight x / (η * ε ^ 3 / 16) :=
      div_le_div_of_nonneg_left (μ.nonneg x) hS.1 hS.2.2.1
    _ = 16 / (η * ε ^ 3) * μ.weight x := by ring

end UnifiedAA.HardSector
