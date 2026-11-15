import UnifiedAA.HardSector.Exclusion
import UnifiedAA.HardSector.Extraction

/-!
# Hard sectors: full-AA failure ⇔ polynomially weighted hard sectors (HS1.8)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, Theorem
`ian:hard-sector-aa-equivalence` and its proof (lines 171-216): (1) ⇒ (2) (via the reduction to
`r > 8` and Corollary `ian:hard-sector-explicit`), (2) ⇒ (3), and the equivalences, using
(3) ⇒ (1) from `HardSector/Exclusion.lean`.

The class family `𝒬 n T` is abstract and assumed `[0,1]`-valued; `FullAA`, `AAWith` and
condition (3) `SmoothSectorWitnesses` are the definitions of `HardSector/Exclusion.lean`.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- Condition (2) of Theorem `ian:hard-sector-aa-equivalence`: for every `A, B ≥ 1` there are
integers `n, T ≥ 1`, a real `r > 8`, `Q ∈ 𝒬 n T` and a set `H` with `μ_n(H) ≥ 1/(64 r^3)` and
`Hard(Q, μ_n(·|H); t, 1/(4r^2), 1/(16r^2))`, where `t = ⌈A(T + r)^B⌉ + 1`. -/
def SetSectorWitnesses (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool))
    (𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)) : Prop :=
  ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
    ∃ n T : ℕ, 1 ≤ n ∧ 1 ≤ T ∧ ∃ r : ℝ, 8 < r ∧ ∃ Q ∈ 𝒬 n T, ∃ H : Set (Fin n → Bool),
      1 / (64 * r ^ 3) ≤ (μ n).prob (· ∈ H) ∧
      ∃ hH : 0 < (μ n).prob (· ∈ H),
        Hard Q (condLaw (μ n) H hH) (⌈A * ((T : ℝ) + r) ^ B⌉₊ + 1)
          (1 / (4 * r ^ 2)) (1 / (16 * r ^ 2))
-- LOCK END

/-- The extraction depth for `ε = 1/r`, `η = 1/4` fits into the enlarged
polynomial budget used to witness failure of AA. -/
lemma extraction_depth_le_polynomial_budget {A B r : ℝ} {T : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : 8 < r) :
    ⌈32 / ((1 / r) ^ 5 * (1 / 4 : ℝ) ^ 2)⌉₊ *
        (⌈A * ((T : ℝ) + r) ^ B⌉₊ + 1) ≤
      ⌈(1026 * A) * ((T : ℝ) + r) ^ (B + 5)⌉₊ := by
  let R : ℝ := (T : ℝ) + r
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hrR : r ≤ R := by dsimp [R]; linarith
  have hR1 : 1 ≤ R := hr1.trans hrR
  have hA0 : 0 ≤ A := by linarith
  have hpow : R ≤ R ^ B := Real.self_le_rpow_of_one_le hR1 hB
  have hX : 2 ≤ A * R ^ B := by
    have hmul : R ^ B ≤ A * R ^ B := by
      simpa using mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hR0.le B)
    linarith
  have ht : (⌈A * R ^ B⌉₊ + 1 : ℕ) ≤ (2 * A * R ^ B : ℝ) := by
    have hc := Nat.ceil_lt_add_one (mul_nonneg hA0 (Real.rpow_nonneg hR0.le B))
    push_cast
    linarith
  have hratio : 32 / ((1 / r) ^ 5 * (1 / 4 : ℝ) ^ 2) = 512 * r ^ 5 := by
    field_simp
    ring
  have hK : (⌈512 * r ^ 5⌉₊ : ℝ) ≤ 513 * r ^ 5 := by
    have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 512 * r ^ 5)
    have hp : 1 ≤ r ^ 5 := one_le_pow₀ hr1
    linarith
  have hr5 : r ^ 5 ≤ R ^ 5 := pow_le_pow_left₀ hr0.le hrR 5
  have hprod : (⌈512 * r ^ 5⌉₊ : ℝ) * (⌈A * R ^ B⌉₊ + 1 : ℕ) ≤
      (1026 * A) * R ^ (B + 5) := by
    calc
      _ ≤ (513 * r ^ 5) * (2 * A * R ^ B) :=
        mul_le_mul hK ht (by positivity) (by positivity)
      _ ≤ (513 * R ^ 5) * (2 * A * R ^ B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr5 (by norm_num))
          (by positivity)
      _ = _ := by rw [Real.rpow_add hR0, Real.rpow_ofNat]; ring
  rw [hratio]
  change ⌈512 * r ^ 5⌉₊ * (⌈A * R ^ B⌉₊ + 1) ≤ ⌈(1026 * A) * R ^ (B + 5)⌉₊
  exact_mod_cast hprod.trans (Nat.le_ceil ((1026 * A) * R ^ (B + 5)))

/-- Proof of Theorem `ian:hard-sector-aa-equivalence`, reduction to `ε < 1/8`: if full AA fails
then for every `A', B' ≥ 1` there are `n, T ≥ 1`, `r > 8` and `Q ∈ 𝒬 n T` with
`ℓ_{μ_n}(⌈A'(T + r)^{B'}⌉, Q) > 1/r`. -/
theorem exists_large_r_of_not_fullAA {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)} (h1 : ¬ FullAA μ 𝒬)
    {A' B' : ℝ} (hA' : 1 ≤ A') (hB' : 1 ≤ B') :
    ∃ n T : ℕ, 1 ≤ n ∧ 1 ≤ T ∧ ∃ r : ℝ, 8 < r ∧ ∃ Q ∈ 𝒬 n T,
      1 / r < ell (μ n) ⌈A' * ((T : ℝ) + r) ^ B'⌉₊ Q := by
  classical
  by_contra hfail
  push Not at hfail
  apply h1
  refine ⟨(16 : ℝ) ^ B' * A', B', ?_, hB', ?_⟩
  · have hp : 1 ≤ (16 : ℝ) ^ B' :=
      Real.one_le_rpow (by norm_num) (by linarith)
    nlinarith
  · intro n T hn hT ε hε hε1 Q hQ
    have hT0 : (0 : ℝ) ≤ T := by positivity
    have hr : 0 < ε⁻¹ := inv_pos.mpr hε
    have hr1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1.le
    have hr' : 8 < max ε⁻¹ 16 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hbase : (T : ℝ) + max ε⁻¹ 16 ≤ 16 * ((T : ℝ) + ε⁻¹) := by
      have hm : max ε⁻¹ 16 ≤ 16 * ε⁻¹ := max_le (by linarith) (by linarith)
      linarith
    have hbudget : A' * ((T : ℝ) + max ε⁻¹ 16) ^ B' ≤
        ((16 : ℝ) ^ B' * A') * ((T : ℝ) + ε⁻¹) ^ B' := by
      calc
        _ ≤ A' * (16 * ((T : ℝ) + ε⁻¹)) ^ B' :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hbase (by linarith)) (by linarith)
        _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    apply (ell_le_iff (μ n) Q _ ε).mp
    calc
      _ ≤ ell (μ n) ⌈A' * ((T : ℝ) + max ε⁻¹ 16) ^ B'⌉₊ Q :=
        ell_antitone (μ n) Q (Nat.ceil_mono hbudget)
      _ ≤ 1 / max ε⁻¹ 16 := hfail n T hn hT _ hr' Q hQ
      _ ≤ 1 / ε⁻¹ := one_div_le_one_div_of_le hr (le_max_left _ _)
      _ = ε := by simp

/-- Theorem `ian:hard-sector-aa-equivalence`, (1) ⇒ (2). -/
theorem setSectorWitnesses_of_not_fullAA {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1)
    (h1 : ¬ FullAA μ 𝒬) : SetSectorWitnesses μ 𝒬 := by
  intro A B hA hB
  obtain ⟨n, T, hn, hT, r, hr, Q, hQ, hell⟩ :=
    exists_large_r_of_not_fullAA h1 (A' := 1026 * A) (B' := B + 5)
      (by linarith) (by linarith)
  have hr0 : 0 < r := by linarith
  have hε : 0 < 1 / r := by positivity
  have hε8 : 1 / r < 1 / 8 := one_div_lt_one_div_of_lt (by norm_num) hr
  have hdepth := extraction_depth_le_polynomial_budget (T := T) hA hB hr
  have hell' := hell.trans_le (ell_antitone (μ n) Q hdepth)
  obtain ⟨H, hS, _⟩ := extraction (μ n) (h𝒬 n T Q hQ) (by omega)
    hε hε8 (η := 1 / 4) (by norm_num) (by norm_num) hell'
  have hw : (1 / 4 : ℝ) * (1 / r) ^ 3 / 16 = 1 / (64 * r ^ 3) := by ring
  have ha : (1 / r) ^ 2 / 4 = 1 / (4 * r ^ 2) := by ring
  have hγ : (1 / 4 : ℝ) * (1 / r) ^ 2 / 4 = 1 / (16 * r ^ 2) := by ring
  rw [hw, ha, hγ] at hS
  exact ⟨n, T, hn, hT, r, hr, Q, hQ, H, hS.2.2.1, hS.2.2.2⟩

/-- Theorem `ian:hard-sector-aa-equivalence`, (2) ⇒ (3): `μ_n(·|H) ≤ μ_n/μ_n(H) ≤ 64 r^3 μ_n`. -/
theorem smoothSectorWitnesses_of_setSectorWitnesses {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h2 : SetSectorWitnesses μ 𝒬) : SmoothSectorWitnesses μ 𝒬 := by
  intro A B hA hB
  obtain ⟨n, T, hn, hT, r, hr, Q, hQ, H, hmass, hH, hhard⟩ := h2 A B hA hB
  refine ⟨n, T, hn, hT, r, hr, Q, hQ, condLaw (μ n) H hH, ?_, hhard⟩
  have hr0 : 0 < r := by linarith
  intro x
  calc
    _ ≤ (μ n).weight x / (μ n).prob (· ∈ H) := condLaw_weight_le (μ n) H hH x
    _ ≤ (μ n).weight x / (1 / (64 * r ^ 3)) :=
      div_le_div_of_nonneg_left ((μ n).nonneg x) (by positivity) hmass
    _ = 64 * r ^ 3 * (μ n).weight x := by simp [div_eq_mul_inv, mul_comm]

/-- Theorem `ian:hard-sector-aa-equivalence`, (1) ⇔ (2). -/
theorem not_fullAA_iff_setSectorWitnesses {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) :
    ¬ FullAA μ 𝒬 ↔ SetSectorWitnesses μ 𝒬 := by
  exact ⟨setSectorWitnesses_of_not_fullAA h𝒬, fun h2 =>
    not_fullAA_of_smoothSectorWitnesses h𝒬 (smoothSectorWitnesses_of_setSectorWitnesses h2)⟩

/-- Theorem `ian:hard-sector-aa-equivalence`, (1) ⇔ (3). -/
theorem not_fullAA_iff_smoothSectorWitnesses {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) :
    ¬ FullAA μ 𝒬 ↔ SmoothSectorWitnesses μ 𝒬 := by
  exact ⟨fun h1 => smoothSectorWitnesses_of_setSectorWitnesses
    (setSectorWitnesses_of_not_fullAA h𝒬 h1), not_fullAA_of_smoothSectorWitnesses h𝒬⟩

end UnifiedAA.HardSector
