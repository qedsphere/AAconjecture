import UnifiedAA.InfluencePotential

/-! Finite Walsh expansions and the degree bound on squared-flip influence.
The elementary character algebra follows the pinned AA bridge, but uses only
the small finite-probability dependency graph. -/

namespace UnifiedAA

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def walsh (S : Finset I) (x : I → Bool) : ℝ :=
  ∏ i ∈ S, if x i then (-1 : ℝ) else 1

theorem walsh_empty (x : I → Bool) : walsh ∅ x = 1 := by simp [walsh]

theorem walsh_mul (S T : Finset I) (x : I → Bool) :
    walsh S x * walsh T x = walsh (symmDiff S T) x := by
  have hu (U : Finset I) : walsh U x =
      ∏ i, if i ∈ U then (if x i then (-1 : ℝ) else 1) else 1 := by
    exact (Fintype.prod_ite_mem U _).symm
  rw [hu S, hu T, hu (symmDiff S T), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    cases x i <;> simp [Finset.mem_symmDiff, hS, hT]

theorem walsh_flip (S : Finset I) (i : I) (x : I → Bool) :
    walsh S (flip i x) = if i ∈ S then -walsh S x else walsh S x := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    unfold walsh
    rw [← Finset.mul_prod_erase S _ hi, ← Finset.mul_prod_erase S _ hi]
    have hh : (∏ j ∈ S.erase i, if flip i x j then (-1 : ℝ) else 1) =
        ∏ j ∈ S.erase i, if x j then (-1 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [flip, Finset.ne_of_mem_erase hj]
    rw [hh]
    cases hx : x i <;> simp [flip, hx]
  · rw [if_neg hi]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [flip, hji]

theorem uniform_expect_walsh (S : Finset I) :
    (FiniteLaw.uniform (I → Bool)).expect (walsh S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S
    rw [if_pos rfl]
    have he : (walsh (∅ : Finset I)) = fun _ => (1 : ℝ) := funext walsh_empty
    rw [he, FiniteLaw.expect_const]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hinv := FiniteLaw.uniform_expect_equiv (flipEquiv i) (walsh S)
    have hneg : (fun x => walsh S (flipEquiv i x)) =
        (fun x => (-1 : ℝ) * walsh S x) := by
      funext x
      change walsh S (flip i x) = _
      simp [walsh_flip, hi]
    rw [hneg, FiniteLaw.expect_const_mul] at hinv
    linarith

theorem uniform_expect_walsh_mul (S T : Finset I) :
    (FiniteLaw.uniform (I → Bool)).expect (fun x => walsh S x * walsh T x) =
      if S = T then 1 else 0 := by
  simp only [walsh_mul, uniform_expect_walsh, Finset.symmDiff_eq_empty]

theorem FiniteLaw.expect_sum {A J : Type*} [Fintype A] (μ : FiniteLaw A)
    (s : Finset J) (f : J → A → ℝ) :
    μ.expect (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, μ.expect (f j) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Parseval for an explicitly supplied finite Walsh expansion. -/
theorem walsh_parseval (c : Finset I → ℝ) :
    (FiniteLaw.uniform (I → Bool)).expect
      (fun x => (∑ S, c S * walsh S x) ^ 2) = ∑ S, c S ^ 2 := by
  have hexpand (x : I → Bool) : (∑ S, c S * walsh S x) ^ 2 =
      ∑ S : Finset I, ∑ T : Finset I, (c S * c T) * (walsh S x * walsh T x) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    ring
  simp_rw [hexpand, FiniteLaw.expect_sum, FiniteLaw.expect_const_mul,
    uniform_expect_walsh_mul]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_eq_single S]
  · simp [pow_two]
  · intro T _ hT
    simp [Ne.symm hT]
  · simp

/-- A Walsh-degree bound is an actual character expansion, with zero
coefficients above the stated degree. -/
def HasWalshDegree (f : (I → Bool) → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset I → ℝ, (∀ S, d < S.card → c S = 0) ∧
    ∀ x, f x = ∑ S, c S * walsh S x

theorem cubeFlipInfluence_expansion (c : Finset I → ℝ) (i : I) :
    cubeFlipInfluence (fun x => ∑ S, c S * walsh S x) i =
      ∑ S, if i ∈ S then 4 * c S ^ 2 else 0 := by
  have hgap (x : I → Bool) :
      (∑ S, c S * walsh S x) - (∑ S, c S * walsh S (flip i x)) =
        ∑ S, (if i ∈ S then 2 * c S else 0) * walsh S x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    rw [walsh_flip]
    by_cases hi : i ∈ S <;> simp [hi] <;> ring
  unfold cubeFlipInfluence
  simp_rw [hgap]
  rw [walsh_parseval]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S <;> simp [hi] <;> ring

theorem totalFlipInfluence_expansion (c : Finset I → ℝ) :
    totalFlipInfluence (fun x => ∑ S, c S * walsh S x) =
      4 * ∑ S, (S.card : ℝ) * c S ^ 2 := by
  unfold totalFlipInfluence
  simp_rw [cubeFlipInfluence_expansion]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Fintype.sum_ite_mem]
  simp
  ring

theorem totalFlipInfluence_le_degree_energy {f : (I → Bool) → ℝ} {d : ℕ}
    (hf : HasWalshDegree f d) :
    totalFlipInfluence f ≤ 4 * d *
      (FiniteLaw.uniform (I → Bool)).expect (fun x => f x ^ 2) := by
  obtain ⟨c, hc, hfc⟩ := hf
  have heq : f = fun x => ∑ S, c S * walsh S x := funext hfc
  rw [heq, totalFlipInfluence_expansion, walsh_parseval, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : d < S.card
  · simp [hc S hS]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast not_lt.mp hS

end UnifiedAA
