import UnifiedAA.FiniteProbability

namespace UnifiedAA

open scoped BigOperators

namespace FiniteLaw

/-- The uniform law on any nonempty finite type. -/
noncomputable def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  weight _ := 1 / (Fintype.card A : ℝ)
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

theorem uniform_expect {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (uniform A).expect f = (∑ a, f a) / (Fintype.card A : ℝ) := by
  unfold expect uniform
  simp only [one_div, ← Finset.mul_sum]
  ring

theorem uniform_expect_equiv {A : Type*} [Fintype A] [Nonempty A]
    (e : A ≃ A) (f : A → ℝ) :
    (uniform A).expect (fun a => f (e a)) = (uniform A).expect f := by
  simp only [uniform_expect]
  rw [e.sum_comp f]

end FiniteLaw

section Cube

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Flip one coordinate of a Boolean table. -/
def flip (i : I) (x : I → Bool) : I → Bool := Function.update x i (!x i)

omit [Fintype I] in
theorem flip_involutive (i : I) : Function.Involutive (flip i) := by
  intro x
  funext j
  by_cases hj : j = i
  · subst j; simp [flip]
  · simp [flip, hj]

def flipEquiv (i : I) : (I → Bool) ≃ (I → Bool) where
  toFun := flip i
  invFun := flip i
  left_inv := flip_involutive i
  right_inv := flip_involutive i

/-- A fair next coordinate can be averaged before or after the other bits,
provided both branch observables ignore this coordinate. -/
theorem uniform_expect_branch (i : I) (f0 f1 : (I → Bool) → ℝ)
    (h0 : ∀ x, f0 (flip i x) = f0 x)
    (h1 : ∀ x, f1 (flip i x) = f1 x) :
    (FiniteLaw.uniform (I → Bool)).expect (fun x => if x i then f1 x else f0 x) =
      ((FiniteLaw.uniform (I → Bool)).expect f0 +
        (FiniteLaw.uniform (I → Bool)).expect f1) / 2 := by
  let μ := FiniteLaw.uniform (I → Bool)
  let f := fun x => if x i then f1 x else f0 x
  have hinv : μ.expect (fun x => f (flip i x)) = μ.expect f :=
    FiniteLaw.uniform_expect_equiv (flipEquiv i) f
  have hsum : ∀ x, f x + f (flip i x) = f0 x + f1 x := by
    intro x
    dsimp [f]
    rw [h0, h1]
    cases hx : x i <;> simp [flip, hx, add_comm]
  have hadd : μ.expect (fun x => f x + f (flip i x)) = μ.expect f0 + μ.expect f1 := by
    simp only [FiniteLaw.expect, hsum, mul_add, Finset.sum_add_distrib]
  have hleft : μ.expect (fun x => f x + f (flip i x)) =
      μ.expect f + μ.expect (fun x => f (flip i x)) := by
    simp only [FiniteLaw.expect, mul_add, Finset.sum_add_distrib]
  change μ.expect f = (μ.expect f0 + μ.expect f1) / 2
  linarith

end Cube
end UnifiedAA
