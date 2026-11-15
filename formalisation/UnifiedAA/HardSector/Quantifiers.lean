import UnifiedAA.HardSector.Quantum

/-!
# Hard sectors: full-AA quantifier reformulations (HS2.1)

Source: `notes/ian/15_hard_sector_sets_asymptotics.tex`, Remark
`ian:hard-sector-polynomial-quantifiers` (property (P)) and Corollary
`ian:hard-sector-resource-equivalence` (property `𝖱(μ)`), in both the smooth and the set
interpretation of sectors.

A `(w,t,a,a/4)`-hard sector of `Q` (file 15, lines 8-10) is, in the smooth interpretation, a law
`ν` with `IsSmoothSector μ_n ν Q t a (a/4) w`, and in the set interpretation a set `H` with
`IsSetSector μ_n H Q t a (a/4) w`. Exponents `p, q, B, b` are real (`Real.rpow`); `⌈·⌉` of a
positive real is `Nat.ceil`. The class family is abstract and `[0,1]`-valued, as in
`HardSector/Equivalence.lean`; the quantum class is a corollary.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- The two interpretations of "sector" (file 15, line 9). -/
inductive SectorKind
  | smooth
  | set

/-- A `(w,t,a,a/4)`-hard sector of `Q` for the law `μ`, in the interpretation `k`. -/
def HasHardSector {I : Type*} [Fintype I] [DecidableEq I] (k : SectorKind)
    (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → ℝ) (w : ℝ) (t : ℕ) (a : ℝ) : Prop :=
  match k with
  | .smooth => ∃ ν : FiniteLaw (I → Bool), IsSmoothSector μ ν Q t a (a / 4) w
  | .set => ∃ H : Set (I → Bool), IsSetSector μ H Q t a (a / 4) w

/-- Property (P) of Remark `ian:hard-sector-polynomial-quantifiers`: polynomial bounds `K, p, q`
fixed before the budget constants `A, B`. -/
def PolynomialSectorProperty (k : SectorKind) (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool))
    (𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)) : Prop :=
  ∃ K p q : ℝ, 1 ≤ K ∧ 1 ≤ p ∧ 1 ≤ q ∧ ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
    ∃ n T : ℕ, 1 ≤ n ∧ 1 ≤ T ∧ ∃ r : ℝ, 8 < r ∧ ∃ Q ∈ 𝒬 n T, ∃ t : ℕ, ∃ w a : ℝ,
      0 < w ∧ w ≤ 1 ∧ 0 < a ∧ a ≤ 1 / 4 ∧
      ⌈A * ((T : ℝ) + r) ^ B⌉₊ < t ∧ w⁻¹ ≤ K * r ^ p ∧ a⁻¹ ≤ K * r ^ q ∧
      HasHardSector k (μ n) Q w t a

/-- Property `𝖱(μ)` of Corollary `ian:hard-sector-resource-equivalence`: for every `b > 0`
there are `A_b, B_b ≥ 1` such that, with `z = 2 + T + a⁻¹`, at every depth
`t ≥ ⌈A_b z^{B_b}⌉` every `(w,t,a,a/4)`-hard sector has `w < z^{-b}`. -/
def ResourceProperty (k : SectorKind) (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool))
    (𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)) : Prop :=
  ∀ b : ℝ, 0 < b → ∃ Ab Bb : ℝ, 1 ≤ Ab ∧ 1 ≤ Bb ∧
    ∀ n T : ℕ, 1 ≤ n → 1 ≤ T → ∀ Q ∈ 𝒬 n T, ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
      ∀ w : ℝ, 0 < w → w ≤ 1 → ∀ t : ℕ,
        ⌈Ab * (2 + (T : ℝ) + a⁻¹) ^ Bb⌉₊ ≤ t → HasHardSector k (μ n) Q w t a →
          w < (2 + (T : ℝ) + a⁻¹) ^ (-b)
-- LOCK END

/-- A hard sector in either interpretation supplies a smooth sector. -/
lemma HasHardSector.exists_smooth {I : Type*} [Fintype I] [DecidableEq I]
    {k : SectorKind} {μ : FiniteLaw (I → Bool)} {Q : (I → Bool) → ℝ}
    {w a : ℝ} {t : ℕ} (h : HasHardSector k μ Q w t a) :
    ∃ ν, IsSmoothSector μ ν Q t a (a / 4) w := by
  cases k with
  | smooth => exact h
  | set =>
    obtain ⟨H, hS⟩ := h
    obtain ⟨hH, _⟩ := hS.2.2.2
    exact ⟨condLaw μ H hH, isSmoothSector_of_isSetSector hS hH⟩

/-- The canonical parameters lie in the required ranges. -/
lemma canonical_parameter_bounds {r : ℝ} (hr : 8 < r) :
    0 < 1 / (64 * r ^ 3) ∧ 1 / (64 * r ^ 3) ≤ 1 ∧
    0 < 1 / (4 * r ^ 2) ∧ 1 / (4 * r ^ 2) ≤ 1 / 4 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have h2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
  have h3 : 1 ≤ r ^ 3 := one_le_pow₀ hr1
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · exact (div_le_one (by positivity)).mpr (by nlinarith)
  · exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)

/-- Failure of full AA supplies the canonical sector in either interpretation. -/
lemma canonical_sector_of_not_fullAA (k : SectorKind)
    {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)}
    {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1)
    (h : ¬ FullAA μ 𝒬) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ n T : ℕ, 1 ≤ n ∧ 1 ≤ T ∧ ∃ r : ℝ, 8 < r ∧ ∃ Q ∈ 𝒬 n T,
      HasHardSector k (μ n) Q (1 / (64 * r ^ 3))
        (⌈A * ((T : ℝ) + r) ^ B⌉₊ + 1) (1 / (4 * r ^ 2)) := by
  obtain ⟨n, T, hn, hT, r, hr, Q, hQ, H, hm, hH, hh⟩ :=
    setSectorWitnesses_of_not_fullAA h𝒬 h A B hA hB
  have hp := canonical_parameter_bounds hr
  have hgamma : 1 / (16 * r ^ 2) = (1 / (4 * r ^ 2)) / 4 := by ring
  rw [hgamma] at hh
  have hS : IsSetSector (μ n) H Q _ _ _ (1 / (64 * r ^ 3)) :=
    ⟨hp.1, hp.2.1, hm, hH, hh⟩
  refine ⟨n, T, hn, hT, r, hr, Q, hQ, ?_⟩
  cases k with
  | set => exact ⟨H, hS⟩
  | smooth => exact ⟨condLaw (μ n) H hH, isSmoothSector_of_isSetSector hS hH⟩

/-- Polynomial inverse-weight bounds control the AA exclusion resource. -/
lemma polynomial_resource_bound {T r w a K p q : ℝ}
    (hT : 1 ≤ T) (hr : 8 < r) (_hw : 0 < w) (ha : 0 < a)
    (hK : 1 ≤ K) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hwi : w⁻¹ ≤ K * r ^ p) (hai : a⁻¹ ≤ K * r ^ q) :
    T + 8 / (3 * w * a) ≤ (1 + 8 * K ^ 2 / 3) * (T + r) ^ (p + q) := by
  have hr0 : 0 < r := by linarith
  have hR : 1 ≤ T + r := by linarith
  have hR0 : 0 ≤ T + r := by linarith
  have hs : 1 ≤ p + q := by linarith
  have hi : w⁻¹ * a⁻¹ ≤ K ^ 2 * r ^ (p + q) := by
    calc
      _ ≤ (K * r ^ p) * (K * r ^ q) :=
        mul_le_mul hwi hai (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hr0]; ring
  have hcost : 8 / (3 * w * a) ≤ (8 * K ^ 2 / 3) * r ^ (p + q) := by
    have heq : 8 / (3 * w * a) = (8 / 3 : ℝ) * (w⁻¹ * a⁻¹) := by
      simp only [div_eq_mul_inv, mul_inv_rev]; ring
    rw [heq]
    nlinarith
  have ht : T ≤ (T + r) ^ (p + q) :=
    (by linarith : T ≤ T + r).trans (Real.self_le_rpow_of_one_le hR hs)
  have hrp : r ^ (p + q) ≤ (T + r) ^ (p + q) :=
    Real.rpow_le_rpow hr0.le (by linarith) (by linarith)
  have hc : 0 ≤ 8 * K ^ 2 / 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hrp hc]

/-- A lower bound on sector weight gives the resource-sensitive AA budget. -/
lemma resource_exclusion_bound {T w a b : ℝ}
    (hT : 0 ≤ T) (_hw : 0 < w) (ha : 0 < a) (hb : 0 < b)
    (hl : (2 + T + a⁻¹) ^ (-b) ≤ w) :
    T + 8 / (3 * w * a) ≤ 4 * (2 + T + a⁻¹) ^ (b + 1) := by
  let z := 2 + T + a⁻¹
  have hai : 0 < a⁻¹ := inv_pos.mpr ha
  have hz1 : 1 ≤ z := by dsimp [z]; linarith
  have hz0 : 0 < z := by linarith
  have hTz : T ≤ z := by dsimp [z]; linarith
  have haz : a⁻¹ ≤ z := by dsimp [z]; linarith
  have hwi : w⁻¹ ≤ z ^ b := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hz0 (-b)) hl
    rw [Real.rpow_neg hz0.le, inv_inv] at hi
    exact hi
  have hprod : w⁻¹ * a⁻¹ ≤ z ^ (b + 1) := by
    calc
      _ ≤ z ^ b * z := mul_le_mul hwi haz (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hz0, Real.rpow_one]
  have hcost : 8 / (3 * w * a) ≤ (8 / 3 : ℝ) * z ^ (b + 1) := by
    have heq : 8 / (3 * w * a) = (8 / 3 : ℝ) * (w⁻¹ * a⁻¹) := by
      simp only [div_eq_mul_inv, mul_inv_rev]; ring
    rw [heq]
    linarith
  have hzpow : z ≤ z ^ (b + 1) :=
    Real.self_le_rpow_of_one_le hz1 (by linarith)
  change T + 8 / (3 * w * a) ≤ 4 * z ^ (b + 1)
  linarith [Real.rpow_nonneg hz0.le (b + 1)]

/-- The resource variable of a canonical witness fits a quadratic budget. -/
lemma canonical_resource_bounds {T r : ℝ} (hT : 1 ≤ T) (hr : 8 < r) :
    2 + T + (1 / (4 * r ^ 2))⁻¹ ≤ 7 * (T + r) ^ (2 : ℕ) ∧
    (2 + T + (1 / (4 * r ^ 2))⁻¹) ^ (- (3 : ℝ)) ≤ 1 / (64 * r ^ 3) := by
  simp only [one_div, inv_inv]
  have hr0 : 0 < r := by linarith
  have hT0 : 0 ≤ T := by linarith
  constructor
  · nlinarith [sq_nonneg (T - 1), mul_nonneg hT0 hr0.le, sq_nonneg r]
  · have hz0 : 0 < 2 + T + 4 * r ^ 2 := by positivity
    rw [Real.rpow_neg hz0.le, Real.rpow_ofNat]
    apply inv_anti₀ (by positivity : 0 < 64 * r ^ 3)
    have hzr : 4 * r ≤ 2 + T + 4 * r ^ 2 := by nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * r) hzr 3
    nlinarith

/-- Remark `ian:hard-sector-polynomial-quantifiers`: for either interpretation, full AA fails iff
property (P) holds. -/
theorem not_fullAA_iff_polynomialSectorProperty (k : SectorKind)
    {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)} {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) :
    ¬ FullAA μ 𝒬 ↔ PolynomialSectorProperty k μ 𝒬 := by
  constructor
  · intro h
    refine ⟨64, 3, 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro A B hA hB
    obtain ⟨n, T, hn, hT, r, hr, Q, hQ, hS⟩ :=
      canonical_sector_of_not_fullAA k h𝒬 h hA hB
    have hp := canonical_parameter_bounds hr
    refine ⟨n, T, hn, hT, r, hr, Q, hQ, _, _, _, hp.1, hp.2.1,
      hp.2.2.1, hp.2.2.2, Nat.lt_succ_self _, ?_, ?_, hS⟩
    · simp only [one_div, inv_inv, Real.rpow_ofNat]
      exact le_rfl
    · simp only [one_div, inv_inv, Real.rpow_ofNat]
      have : 0 ≤ r ^ 2 := sq_nonneg r
      nlinarith
  · rintro ⟨K, p, q, hK, hp, hq, h⟩ ⟨A₀, B₀, hA₀, hB₀, hAA⟩
    let c : ℝ := 8 * K ^ 2 / 3
    let A : ℝ := A₀ * (1 + c) ^ B₀ + 1
    let B : ℝ := (p + q) * B₀
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hA : 1 ≤ A := by
      have : 0 ≤ A₀ * (1 + c) ^ B₀ := mul_nonneg (by linarith) (by positivity)
      dsimp [A]
      linarith
    have hB : 1 ≤ B := by dsimp [B]; nlinarith
    obtain ⟨n, T, hn, hT, r, hr, Q, hQ, t, w, a, hw, hw1, ha, ha1,
      ht, hwi, hai, hS⟩ := h A B hA hB
    obtain ⟨ν, hS⟩ := hS.exists_smooth
    have hexcl := depth_lt_of_aa hAA hn hT hQ (h𝒬 n T Q hQ) hS
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hb := polynomial_resource_bound hT' hr hw ha hK hp hq hwi hai
    have hr0 : 0 < r := by linarith
    have hR : 0 ≤ (T : ℝ) + r := by positivity
    have hbudget : A₀ * ((T : ℝ) + 8 / (3 * w * a)) ^ B₀ ≤
        A * ((T : ℝ) + r) ^ B := by
      calc
        _ ≤ A₀ * ((1 + c) * ((T : ℝ) + r) ^ (p + q)) ^ B₀ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hb (by linarith)) (by linarith)
        _ = (A₀ * (1 + c) ^ B₀) * ((T : ℝ) + r) ^ B := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hR _),
            ← Real.rpow_mul hR]
          dsimp [B]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith)
          (Real.rpow_nonneg hR _)
    have hceil := Nat.ceil_mono hbudget
    omega

/-- Corollary `ian:hard-sector-resource-equivalence`: for either interpretation, full AA holds
iff `𝖱(μ)` holds. -/
theorem fullAA_iff_resourceProperty (k : SectorKind)
    {μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)} {𝒬 : ∀ n : ℕ, ℕ → Set ((Fin n → Bool) → ℝ)}
    (h𝒬 : ∀ n T, ∀ Q ∈ 𝒬 n T, ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) :
    FullAA μ 𝒬 ↔ ResourceProperty k μ 𝒬 := by
  classical
  constructor
  · rintro ⟨A₀, B₀, hA₀, hB₀, hAA⟩ b hb
    let Ab : ℝ := A₀ * (4 : ℝ) ^ B₀ + 1
    let Bb : ℝ := (b + 1) * B₀
    have hAb : 1 ≤ Ab := by
      have : 0 ≤ A₀ * (4 : ℝ) ^ B₀ := mul_nonneg (by linarith) (by positivity)
      dsimp [Ab]
      linarith
    have hBb : 1 ≤ Bb := by dsimp [Bb]; nlinarith
    refine ⟨Ab, Bb, hAb, hBb, ?_⟩
    intro n T hn hT Q hQ a ha ha1 w hw hw1 t ht hS
    by_contra hl
    have hl : (2 + (T : ℝ) + a⁻¹) ^ (-b) ≤ w := le_of_not_gt hl
    obtain ⟨ν, hS⟩ := hS.exists_smooth
    have hexcl := depth_lt_of_aa hAA hn hT hQ (h𝒬 n T Q hQ) hS
    let z : ℝ := 2 + (T : ℝ) + a⁻¹
    have hz0 : 0 < z := by dsimp [z]; positivity
    have hbase := resource_exclusion_bound (by positivity : (0 : ℝ) ≤ T) hw ha hb hl
    have hbudget : A₀ * ((T : ℝ) + 8 / (3 * w * a)) ^ B₀ ≤ Ab * z ^ Bb := by
      calc
        _ ≤ A₀ * (4 * z ^ (b + 1)) ^ B₀ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hbase (by linarith)) (by linarith)
        _ = (A₀ * (4 : ℝ) ^ B₀) * z ^ Bb := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hz0.le _),
            ← Real.rpow_mul hz0.le]
          dsimp [Bb]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [Ab]; linarith)
          (Real.rpow_nonneg hz0.le _)
    have hceil := Nat.ceil_mono hbudget
    change ⌈Ab * z ^ Bb⌉₊ ≤ t at ht
    omega
  · intro hR
    by_contra hAA
    obtain ⟨A, B, hA, hB, h⟩ := hR 3 (by norm_num)
    have hA' : 1 ≤ A * (7 : ℝ) ^ B := by
      have hp : 1 ≤ (7 : ℝ) ^ B := Real.one_le_rpow (by norm_num) (by linarith)
      nlinarith
    have hB' : 1 ≤ 2 * B := by linarith
    obtain ⟨n, T, hn, hT, r, hr, Q, hQ, hS⟩ :=
      canonical_sector_of_not_fullAA k h𝒬 hAA hA' hB'
    have hp := canonical_parameter_bounds hr
    have hr0 : 0 < r := by linarith
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    obtain ⟨hbase, hweight⟩ := canonical_resource_bounds hT' hr
    have hR0 : 0 ≤ (T : ℝ) + r := by positivity
    have hz0 : 0 < 2 + (T : ℝ) + (1 / (4 * r ^ 2))⁻¹ := by positivity
    have hbudget : A * (2 + (T : ℝ) + (1 / (4 * r ^ 2))⁻¹) ^ B ≤
        (A * (7 : ℝ) ^ B) * ((T : ℝ) + r) ^ (2 * B) := by
      calc
        _ ≤ A * (7 * ((T : ℝ) + r) ^ (2 : ℕ)) ^ B :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hz0.le hbase (by linarith)) (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (by positivity),
            ← Real.rpow_natCast_mul hR0 2 B]
          norm_num
          ring
    have ht : ⌈A * (2 + (T : ℝ) + (1 / (4 * r ^ 2))⁻¹) ^ B⌉₊ ≤
        ⌈(A * (7 : ℝ) ^ B) * ((T : ℝ) + r) ^ (2 * B)⌉₊ + 1 :=
      (Nat.ceil_mono hbudget).trans (Nat.le_succ _)
    have hlt := h n T hn hT Q hQ _ hp.2.2.1 hp.2.2.2 _ hp.1 hp.2.1 _ ht hS
    exact (not_lt_of_ge hweight) hlt

/-- Remark `ian:hard-sector-polynomial-quantifiers` for the quantum class `\mathcal Q_{n,T}`. -/
theorem quantum_not_fullAA_iff_polynomialSectorProperty (k : SectorKind)
    (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)) :
    ¬ FullAA μ QuantumClass ↔ PolynomialSectorProperty k μ QuantumClass := by
  exact not_fullAA_iff_polynomialSectorProperty k
    (fun _ _ _ hQ x => quantumClass_mem_unit hQ x)

/-- Corollary `ian:hard-sector-resource-equivalence` for the quantum class `\mathcal Q_{n,T}`. -/
theorem quantum_fullAA_iff_resourceProperty (k : SectorKind)
    (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)) :
    FullAA μ QuantumClass ↔ ResourceProperty k μ QuantumClass := by
  exact fullAA_iff_resourceProperty k
    (fun _ _ _ hQ x => quantumClass_mem_unit hQ x)

end UnifiedAA.HardSector
