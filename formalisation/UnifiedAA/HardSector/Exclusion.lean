import UnifiedAA.HardSector.Forward
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Hard sectors: full AA excludes polynomially weighted hard sectors (HS1.4)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`: the property (AA)
(`ian:hard-sector-aa-definition`), Lemma `ian:hard-sector-aa-exclusion`, and the implication
(3) ⇒ (1) of Theorem `ian:hard-sector-aa-equivalence`.

The quantum class `\mathcal Q_{n,T}` is a parameter: an arbitrary family `𝒬 n T` of functions
`(Fin n → Bool) → ℝ`, assumed `[0,1]`-valued where needed (acceptance probabilities are).
`ℓ_μ(L,Q) ≤ ε` is encoded as "some `D ∈ \mathcal D_L` has `E_μ|D - Q| ≤ ε`". The TeX ceiling
`⌈·⌉` of a positive real is `Nat.ceil`; exponents `B₀, B` are real (`Real.rpow`).
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- Property (AA) (`ian:hard-sector-aa-definition`) with fixed constants `A₀, B₀`: for all
`n, T ≥ 1`, `ε ∈ (0,1)` and `Q ∈ 𝒬 n T`, some tree of depth at most `⌈A₀(T + 1/ε)^{B₀}⌉` has
`E_{μ_n}|D - Q| ≤ ε`. -/
def AAWith (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)) (𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ))
    (A₀ B₀ : ℝ) : Prop :=
  ∀ n T : ℕ, 1 ≤ n → 1 ≤ T → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ Q ∈ 𝒬 n T,
    ∃ D ∈ DepthTrees (Fin n) ⌈A₀ * ((T : ℝ) + ε⁻¹) ^ B₀⌉₊,
      (μ n).expect (fun x => |D.eval x - Q x|) ≤ ε

/-- Full AA (`ian:hard-sector-aa-definition`): (AA) holds for some constants `A₀, B₀ ≥ 1`. -/
def FullAA (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool))
    (𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)) : Prop :=
  ∃ A₀ B₀ : ℝ, 1 ≤ A₀ ∧ 1 ≤ B₀ ∧ AAWith μ 𝒬 A₀ B₀

/-- Condition (3) of Theorem `ian:hard-sector-aa-equivalence`: for every `A, B ≥ 1` there are
integers `n, T ≥ 1`, a real `r > 8`, `Q ∈ 𝒬 n T` and a law `ν` with `ν ≤ 64 r^3 μ_n` and
`Hard(Q, ν; t, 1/(4r^2), 1/(16r^2))`, where `t = ⌈A(T + r)^B⌉ + 1`. -/
def SmoothSectorWitnesses (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool))
    (𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)) : Prop :=
  ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
    ∃ n T : ℕ, 1 ≤ n ∧ 1 ≤ T ∧ ∃ r : ℝ, 8 < r ∧ ∃ Q ∈ 𝒬 n T, ∃ ν : FiniteLaw (Fin n → Bool),
      (∀ x, ν.weight x ≤ 64 * r ^ 3 * (μ n).weight x) ∧
      Hard Q ν (⌈A * ((T : ℝ) + r) ^ B⌉₊ + 1) (1 / (4 * r ^ 2)) (1 / (16 * r ^ 2))
-- LOCK END

/-- Lemma `ian:hard-sector-aa-exclusion`: if (AA) holds with constants `A₀, B₀`, `n, T ≥ 1`,
`Q ∈ 𝒬 n T` is `[0,1]`-valued, and `ν` is a smooth sector of `μ_n` of weight `w` with
`Hard(Q, ν; t, a, a/4)`, then `t < ⌈A₀(T + 8/(3wa))^{B₀}⌉`. -/
theorem depth_lt_of_aa {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)} {A₀ B₀ : ℝ} (hAA : AAWith μ 𝒬 A₀ B₀)
    {n T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) {Q : (Fin n → Bool) → ℝ} (hQ𝒬 : Q ∈ 𝒬 n T)
    (hQ : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) {ν : FiniteLaw (Fin n → Bool)} {t : ℕ} {a w : ℝ}
    (hS : IsSmoothSector (μ n) ν Q t a (a / 4) w) :
    t < ⌈A₀ * ((T : ℝ) + 8 / (3 * w * a)) ^ B₀⌉₊ := by
  have hw : 0 < w := hS.1
  have hw1 : w ≤ 1 := hS.2.1
  have ha : 0 < a := lt_trans hS.2.2.2.1 hS.2.2.2.2.1
  have ha1 : a ≤ 1 / 4 := hS.2.2.2.2.2.1
  let e := 3 * w * a / 8
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e < 1 := by
    have : w * a ≤ 1 / 4 := by
      calc
        w * a ≤ 1 * a := mul_le_mul_of_nonneg_right hw1 ha.le
        _ ≤ 1 / 4 := by simpa using ha1
    dsimp [e]
    nlinarith
  have hinv : e⁻¹ = 8 / (3 * w * a) := by
    dsimp [e]
    rw [inv_div]
  by_contra hdepth
  have hle : ⌈A₀ * ((T : ℝ) + e⁻¹) ^ B₀⌉₊ ≤ t := by
    rw [hinv]
    exact Nat.le_of_not_gt hdepth
  obtain ⟨D, hD, herr⟩ := hAA n T hn hT e he he1 Q hQ𝒬
  have hbound := forward_bound hQ hS (depthTrees_mono hle hD)
  simp_rw [abs_sub_comm (Q _) (D.eval _)] at hbound
  dsimp [e] at he herr
  nlinarith

/-- Theorem `ian:hard-sector-aa-equivalence`, (3) ⇒ (1): if every class function is
`[0,1]`-valued and condition (3) holds, full AA fails. -/
theorem not_fullAA_of_smoothSectorWitnesses {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1)
    (h3 : SmoothSectorWitnesses μ 𝒬) : ¬ FullAA μ 𝒬 := by
  rintro ⟨A₀, B₀, hA₀, hB₀, hAA⟩
  have hA₀0 : 0 ≤ A₀ := by linarith
  have hB₀0 : 0 ≤ B₀ := by linarith
  let A : ℝ := (2 : ℝ) ^ (10 * B₀) * A₀
  let B : ℝ := 5 * B₀
  have hA : 1 ≤ A := by
    have hp : 1 ≤ (2 : ℝ) ^ (10 * B₀) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    dsimp [A]
    nlinarith
  have hB : 1 ≤ B := by dsimp [B]; linarith
  obtain ⟨n, T, hn, hT, r, hr, Q, hQ, ν, hdom, hhard⟩ := h3 A B hA hB
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) ≤ T := by positivity
  let w : ℝ := 1 / (64 * r ^ 3)
  let a : ℝ := 1 / (4 * r ^ 2)
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    have hp : 1 ≤ r ^ 3 := one_le_pow₀ hr1
    dsimp [w]
    exact (div_le_one (by positivity)).mpr (by nlinarith)
  have hgamma : 1 / (16 * r ^ 2) = a / 4 := by
    dsimp [a]
    ring
  have hS : IsSmoothSector (μ n) ν Q (⌈A * ((T : ℝ) + r) ^ B⌉₊ + 1)
      a (a / 4) w := by
    refine ⟨hw, hw1, ?_, ?_⟩
    · intro x
      dsimp [w]
      rw [div_mul_eq_mul_div, one_mul]
      apply (div_le_iff₀ (by positivity : 0 < 64 * r ^ 3)).mpr
      simpa [mul_comm] using hdom x
    · rw [hgamma] at hhard
      exact hhard
  have hexcl := depth_lt_of_aa hAA hn hT hQ (h𝒬 n T Q hQ) hS
  have hinv : 8 / (3 * w * a) = 2048 / 3 * r ^ 5 := by
    dsimp [w, a]
    field_simp [hrne]
    ring
  have hbase : (T : ℝ) + 8 / (3 * w * a) ≤ (2 : ℝ) ^ (10 : ℕ) *
      ((T : ℝ) + r) ^ (5 : ℕ) := by
    rw [hinv]
    have hpow : (T : ℝ) + r ^ 5 ≤ ((T : ℝ) + r) ^ 5 := by
      calc
        (T : ℝ) + r ^ 5 ≤ (T : ℝ) ^ 5 + r ^ 5 :=
          add_le_add (le_self_pow₀ hT1 (by decide : 5 ≠ 0)) le_rfl
        _ ≤ _ := pow_add_pow_le hT0 hr0.le (by decide)
    have hr5 : 0 ≤ r ^ 5 := by positivity
    norm_num
    nlinarith
  have hR : 0 ≤ (T : ℝ) + r := by positivity
  have hpower : (((2 : ℝ) ^ (10 : ℕ) * ((T : ℝ) + r) ^ (5 : ℕ)) : ℝ) ^ B₀ =
      (2 : ℝ) ^ (10 * B₀) * ((T : ℝ) + r) ^ (5 * B₀) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 10 B₀,
      ← Real.rpow_natCast_mul hR 5 B₀]
    norm_num
  have hbudget : A₀ * ((T : ℝ) + 8 / (3 * w * a)) ^ B₀ ≤
      A * ((T : ℝ) + r) ^ B := by
    calc
      A₀ * ((T : ℝ) + 8 / (3 * w * a)) ^ B₀ ≤
          A₀ * ((2 : ℝ) ^ (10 : ℕ) * ((T : ℝ) + r) ^ (5 : ℕ)) ^ B₀ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase hB₀0) hA₀0
      _ = A * ((T : ℝ) + r) ^ B := by rw [hpower]; dsimp [A, B]; ring
  have hceil := Nat.ceil_mono hbudget
  omega

end UnifiedAA.HardSector
