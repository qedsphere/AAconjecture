import UnifiedAA.CubeConditioning

/-!
The exact one-query potential drop used by scalar simulation. This identity
holds for every real function on a finite Boolean cube; no degree or AA
hypothesis is needed. The influence normalization is the squared flip gap.
-/

namespace UnifiedAA

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def cubeFlipInfluence (f : (I → Bool) → ℝ) (j : I) : ℝ :=
  (FiniteLaw.uniform (I → Bool)).expect (fun x => (f x - f (flip j x)) ^ 2)

noncomputable def totalFlipInfluence (f : (I → Bool) → ℝ) : ℝ :=
  ∑ j, cubeFlipInfluence f j

theorem cubeFlipInfluence_nonneg (f : (I → Bool) → ℝ) (j : I) :
    0 ≤ cubeFlipInfluence f j := by
  unfold cubeFlipInfluence
  calc
    0 = (FiniteLaw.uniform (I → Bool)).expect (fun _ => (0 : ℝ)) :=
      ((FiniteLaw.uniform (I → Bool)).expect_const 0).symm
    _ ≤ (FiniteLaw.uniform (I → Bool)).expect
          (fun x => (f x - f (flip j x)) ^ 2) :=
      (FiniteLaw.uniform (I → Bool)).expect_mono (fun x => sq_nonneg _)

theorem totalFlipInfluence_nonneg (f : (I → Bool) → ℝ) :
    0 ≤ totalFlipInfluence f := by
  unfold totalFlipInfluence
  exact Finset.sum_nonneg (fun j _ => cubeFlipInfluence_nonneg f j)

omit [Fintype I] in
theorem update_flip_commute (i j : I) (hji : j ≠ i) (b : Bool) (x : I → Bool) :
    Function.update (flip j x) i b = flip j (Function.update x i b) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [flip, hji, Ne.symm hji]
  · by_cases hkj : k = j
    · subst k
      simp [flip, hki]
    · simp [flip, hki, hkj]

theorem cubeFlipInfluence_restrict_other (f : (I → Bool) → ℝ) (i j : I)
    (hji : j ≠ i) :
    cubeFlipInfluence f j =
      (cubeFlipInfluence (restrictBit f i false) j +
       cubeFlipInfluence (restrictBit f i true) j) / 2 := by
  let gap : (I → Bool) → ℝ := fun x => (f x - f (flip j x)) ^ 2
  have hb (b : Bool) :
      (FiniteLaw.uniform (I → Bool)).expect (restrictBit gap i b) =
        cubeFlipInfluence (restrictBit f i b) j := by
    unfold cubeFlipInfluence
    congr 1
    funext x
    simp only [restrictBit, gap]
    rw [update_flip_commute i j hji b x]
  have h := uniform_expect_restrictBit gap i
  change cubeFlipInfluence f j = _ at h
  rw [hb false, hb true] at h
  exact h

theorem cubeFlipInfluence_restrict_same (f : (I → Bool) → ℝ) (i : I)
    (b : Bool) : cubeFlipInfluence (restrictBit f i b) i = 0 := by
  have hfun :
      (fun x => (restrictBit f i b x - restrictBit f i b (flip i x)) ^ 2) =
        (fun _ => (0 : ℝ)) := by
    funext x
    rw [restrictBit_flip]
    ring
  unfold cubeFlipInfluence
  rw [hfun, FiniteLaw.expect_const]

/-- The expected decrease of total squared-flip influence after reading a
fresh coordinate equals the influence of that coordinate. -/
theorem totalFlipInfluence_drop (f : (I → Bool) → ℝ) (i : I) :
    totalFlipInfluence f -
      (totalFlipInfluence (restrictBit f i false) +
       totalFlipInfluence (restrictBit f i true)) / 2 =
      cubeFlipInfluence f i := by
  let f0 := restrictBit f i false
  let f1 := restrictBit f i true
  have hterm (j : I) : cubeFlipInfluence f j =
      (cubeFlipInfluence f0 j + cubeFlipInfluence f1 j) / 2 +
        if j = i then cubeFlipInfluence f i else 0 := by
    by_cases hji : j = i
    · subst j
      simp [f0, f1, cubeFlipInfluence_restrict_same]
    · simp [hji, f0, f1, cubeFlipInfluence_restrict_other f i j hji]
  have hsum : totalFlipInfluence f =
      (totalFlipInfluence f0 + totalFlipInfluence f1) / 2 +
        cubeFlipInfluence f i := by
    calc
      totalFlipInfluence f =
          ∑ j, ((cubeFlipInfluence f0 j + cubeFlipInfluence f1 j) / 2 +
            if j = i then cubeFlipInfluence f i else 0) := by
        unfold totalFlipInfluence
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
      _ = _ := by
        simp only [totalFlipInfluence, Finset.sum_add_distrib, div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp
  dsimp [f0, f1] at hsum
  linarith

end UnifiedAA
