import UnifiedAA.UniformHashing

/-! Finite independent products, repetition and multi-bit function hashing.
Random tables have no oracle-query cost here; this is not yet the compact
affine seed family used in the manuscript. -/

namespace UnifiedAA

open scoped BigOperators

namespace FiniteLaw

variable {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]

/-- Independent coordinates, with each coordinate's specified finite law. -/
def independent (μ : J → FiniteLaw A) : FiniteLaw (J → A) where
  weight x := ∏ j, (μ j).weight (x j)
  nonneg x := by
    apply Finset.prod_induction
    · intro a b ha hb
      exact mul_nonneg ha hb
    · exact zero_le_one
    · intro j _
      exact (μ j).nonneg (x j)
  total := by
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.total, Finset.prod_const_one]

/-- Independence is proved from the product weights, not assumed separately. -/
theorem prob_independent (μ : J → FiniteLaw A) (P : J → A → Prop) :
    (independent μ).prob (fun x => ∀ j, P j (x j)) = ∏ j, (μ j).prob (P j) := by
  classical
  have hpoint (x : J → A) :
      (if ∀ j, P j (x j) then ∏ j, (μ j).weight (x j) else 0) =
        ∏ j, if P j (x j) then (μ j).weight (x j) else 0 := by
    by_cases hx : ∀ j, P j (x j)
    · simp [hx]
    · rw [if_neg hx]
      obtain ⟨j, hj⟩ := not_forall.mp hx
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
  simp only [prob, independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ j, P j (x j)
  · simpa only [if_pos hx] using hpoint x
  · simpa only [if_neg hx] using hpoint x

theorem prob_all_repetitions (μ : FiniteLaw A) (P : A → Prop) (r : ℕ) :
    (independent (fun _ : Fin r => μ)).prob (fun x => ∀ j, P (x j)) =
      (μ.prob P) ^ r := by
  rw [prob_independent]
  simp

/-- The failure probability of independent repetitions is the single-run
failure probability raised to the number of runs. -/
theorem prob_no_success (μ : FiniteLaw A) (success : A → Prop) (r : ℕ) :
    (independent (fun _ : Fin r => μ)).prob (fun x => ¬ ∃ j, success (x j)) =
      (1 - μ.prob success) ^ r := by
  have heq : (fun x : Fin r → A => ¬ ∃ j, success (x j)) =
      (fun x => ∀ j, ¬ success (x j)) := by
    funext x
    exact propext not_exists
  rw [heq, prob_all_repetitions μ (fun a => ¬ success a) r, prob_not]

end FiniteLaw

/-- Independent Boolean hash tables give exactly `1/2^k` pair collisions.
This family works for every finite input type, without an affine encoding. -/
theorem independent_bool_hash_collision {Y : Type*} [Fintype Y] [DecidableEq Y]
    (k : ℕ) (y z : Y) (hyz : y ≠ z) :
    (FiniteLaw.independent (fun _ : Fin k => FiniteLaw.uniform (Y → Bool))).prob
      (fun h => (fun j => h j y) = (fun j => h j z)) = 1 / (2 : ℝ) ^ k := by
  have heq : (fun h : Fin k → Y → Bool => (fun j => h j y) = (fun j => h j z)) =
      (fun h => ∀ j, h j y = h j z) := by
    funext h
    exact propext funext_iff
  rw [heq, FiniteLaw.prob_all_repetitions (FiniteLaw.uniform (Y → Bool))
    (fun h => h y = h z) k, uniform_bool_hash_collision y z hyz]
  rw [div_pow, one_pow]

end UnifiedAA
