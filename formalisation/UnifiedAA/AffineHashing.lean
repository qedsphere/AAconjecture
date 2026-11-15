import UnifiedAA.IndependentSampling
import UnifiedAA.FourierPotential

/-! A compact affine Boolean hash family. A row computes the parity of the
input bits selected by that row; the extra seed bit is the affine offset.
Independent rows give exactly 1/2^k collision probability. -/

namespace UnifiedAA

variable {I : Type*} [Fintype I] [DecidableEq I]

def trueCoordinates (x : I → Bool) : Finset I := Finset.univ.filter (fun i => x i = true)

theorem trueCoordinates_injective : Function.Injective (trueCoordinates (I := I)) := by
  intro x y h
  funext i
  have hi : (x i = true) ↔ (y i = true) := by
    have := Finset.ext_iff.mp h i
    simpa [trueCoordinates] using this
  cases hx : x i <;> cases hy : y i <;> simp_all

theorem walsh_eq_one_or_neg_one (S : Finset I) (x : I → Bool) :
    walsh S x = 1 ∨ walsh S x = -1 := by
  have hs : walsh S x ^ 2 = 1 := by
    simpa [pow_two, walsh_empty] using walsh_mul S S x
  exact sq_eq_one_iff.mp hs

/-- True when the parity dot product of the row and input is odd. -/
noncomputable def linearHashBit (row x : I → Bool) : Bool :=
  decide (walsh (trueCoordinates x) row = -1)

noncomputable def affineHashBit (seed : (I → Bool) × Bool) (x : I → Bool) : Bool :=
  Bool.xor (linearHashBit seed.1 x) seed.2

theorem uniform_linear_hash_collision (x y : I → Bool) (hxy : x ≠ y) :
    (FiniteLaw.uniform (I → Bool)).prob
      (fun row => linearHashBit row x = linearHashBit row y) = 1 / 2 := by
  classical
  let S := trueCoordinates x
  let T := trueCoordinates y
  have hST : S ≠ T := fun h => hxy (trueCoordinates_injective h)
  have hdiff : symmDiff S T ≠ ∅ := by
    intro h
    exact hST (Finset.symmDiff_eq_empty.mp h)
  have hpoint (row : I → Bool) :
      (if linearHashBit row x = linearHashBit row y then (1 : ℝ) else 0) =
        1 / 2 + (1 / 2) * walsh (symmDiff S T) row := by
    rw [← walsh_mul]
    change (if decide (walsh S row = -1) = decide (walsh T row = -1) then (1 : ℝ) else 0) = _
    rcases walsh_eq_one_or_neg_one S row with hs | hs <;>
      rcases walsh_eq_one_or_neg_one T row with ht | ht <;>
      norm_num [hs, ht]
  rw [prob_eq_expect_indicator]
  simp_rw [hpoint]
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const, FiniteLaw.expect_const_mul,
    uniform_expect_walsh, if_neg hdiff]
  ring

noncomputable def affineRowLaw (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteLaw ((I → Bool) × Bool) :=
  (FiniteLaw.uniform (I → Bool)).prod (FiniteLaw.uniform Bool)

theorem affineHashBit_collision_iff (seed : (I → Bool) × Bool) (x y : I → Bool) :
    affineHashBit seed x = affineHashBit seed y ↔ linearHashBit seed.1 x = linearHashBit seed.1 y := by
  unfold affineHashBit
  cases seed.2 <;> cases linearHashBit seed.1 x <;> cases linearHashBit seed.1 y <;> decide

theorem uniform_affine_hash_bit_collision (x y : I → Bool) (hxy : x ≠ y) :
    (affineRowLaw I).prob (fun seed => affineHashBit seed x = affineHashBit seed y) = 1 / 2 := by
  classical
  have heq : (fun seed : (I → Bool) × Bool => affineHashBit seed x = affineHashBit seed y) =
      (fun seed => linearHashBit seed.1 x = linearHashBit seed.1 y) := by
    funext seed
    exact propext (affineHashBit_collision_iff seed x y)
  rw [heq]
  unfold affineRowLaw
  rw [(FiniteLaw.uniform (I → Bool)).prob_prod (FiniteLaw.uniform Bool)
    (fun row _ => linearHashBit row x = linearHashBit row y)]
  have hconst (row : I → Bool) :
      (FiniteLaw.uniform Bool).prob (fun _ => linearHashBit row x = linearHashBit row y) =
        if linearHashBit row x = linearHashBit row y then 1 else 0 := by
    unfold FiniteLaw.prob
    by_cases h : linearHashBit row x = linearHashBit row y
    · simp only [if_pos h]
      exact (FiniteLaw.uniform Bool).total
    · simp [h]
  simp_rw [hconst]
  rw [← prob_eq_expect_indicator, uniform_linear_hash_collision x y hxy]

noncomputable def affineHashLaw (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) :
    FiniteLaw (Fin k → (I → Bool) × Bool) :=
  FiniteLaw.independent (fun _ => affineRowLaw I)

noncomputable def affineHash {k : ℕ} (seed : Fin k → (I → Bool) × Bool)
    (x : I → Bool) : Fin k → Bool := fun j => affineHashBit (seed j) x

/-- The exact collision probability for k independent affine parity rows. -/
theorem uniform_affine_hash_collision (k : ℕ) (x y : I → Bool) (hxy : x ≠ y) :
    (affineHashLaw I k).prob (fun seed => affineHash seed x = affineHash seed y) =
      1 / (2 : ℝ) ^ k := by
  have heq : (fun seed : Fin k → (I → Bool) × Bool => affineHash seed x = affineHash seed y) =
      (fun seed => ∀ j, affineHashBit (seed j) x = affineHashBit (seed j) y) := by
    funext seed
    exact propext funext_iff
  rw [heq, affineHashLaw, FiniteLaw.prob_all_repetitions (affineRowLaw I)
    (fun seed => affineHashBit seed x = affineHashBit seed y) k,
    uniform_affine_hash_bit_collision x y hxy, div_pow, one_pow]

end UnifiedAA
