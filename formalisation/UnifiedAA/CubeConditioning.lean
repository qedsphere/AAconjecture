import UnifiedAA.Uniform

/-!
One-coordinate conditioning on the uniform Boolean cube. These identities
connect a branch of a fresh decision tree to the restricted target function.
-/

namespace UnifiedAA

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Fix a coordinate while leaving every other Boolean coordinate free. -/
def restrictBit (f : (I → Bool) → ℝ) (i : I) (b : Bool) : (I → Bool) → ℝ :=
  fun x => f (Function.update x i b)

omit [Fintype I] in
theorem restrictBit_flip (f : (I → Bool) → ℝ) (i : I) (b : Bool)
    (x : I → Bool) : restrictBit f i b (flip i x) = restrictBit f i b x := by
  unfold restrictBit
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

omit [Fintype I] in
theorem restrictBit_at_value (f : (I → Bool) → ℝ) (i : I) (x : I → Bool) :
    restrictBit f i (x i) x = f x := by
  unfold restrictBit
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- Averaging a function over the cube is averaging its two restrictions. -/
theorem uniform_expect_restrictBit (f : (I → Bool) → ℝ) (i : I) :
    (FiniteLaw.uniform (I → Bool)).expect f =
      ((FiniteLaw.uniform (I → Bool)).expect (restrictBit f i false) +
       (FiniteLaw.uniform (I → Bool)).expect (restrictBit f i true)) / 2 := by
  have h := uniform_expect_branch i (restrictBit f i false) (restrictBit f i true)
    (restrictBit_flip f i false) (restrictBit_flip f i true)
  have hfun : f = (fun x => if x i then restrictBit f i true x else restrictBit f i false x) := by
    funext x
    cases hx : x i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · simpa [hx] using (restrictBit_at_value f i x).symm
    · simpa [hx] using (restrictBit_at_value f i x).symm
  calc
    (FiniteLaw.uniform (I → Bool)).expect f =
        (FiniteLaw.uniform (I → Bool)).expect
          (fun x => if x i then restrictBit f i true x else restrictBit f i false x) :=
      congrArg _ hfun
    _ = _ := h

/-- Exact mean squared error split for a one-bit estimator. -/
theorem uniform_mse_branch (f : (I → Bool) → ℝ) (i : I) (c0 c1 : ℝ) :
    (FiniteLaw.uniform (I → Bool)).expect
        (fun x => (f x - if x i then c1 else c0) ^ 2) =
      ((FiniteLaw.uniform (I → Bool)).expect
          (fun x => (restrictBit f i false x - c0) ^ 2) +
       (FiniteLaw.uniform (I → Bool)).expect
          (fun x => (restrictBit f i true x - c1) ^ 2)) / 2 := by
  let f0 : (I → Bool) → ℝ := fun x => (restrictBit f i false x - c0) ^ 2
  let f1 : (I → Bool) → ℝ := fun x => (restrictBit f i true x - c1) ^ 2
  have h := uniform_expect_branch i f0 f1
    (fun x => by simp only [f0, restrictBit_flip])
    (fun x => by simp only [f1, restrictBit_flip])
  have hfun :
      (fun x => (f x - if x i then c1 else c0) ^ 2) =
      (fun x => if x i then f1 x else f0 x) := by
    funext x
    cases hx : x i <;> simp only [Bool.false_eq_true, ↓reduceIte, f0, f1]
    · have hv : restrictBit f i false x = f x := by
        simpa only [hx] using restrictBit_at_value f i x
      rw [hv]
    · have hv : restrictBit f i true x = f x := by
        simpa only [hx] using restrictBit_at_value f i x
      rw [hv]
  rw [hfun]
  exact h

end UnifiedAA
