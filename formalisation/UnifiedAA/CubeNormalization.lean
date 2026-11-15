import UnifiedAA.PolynomialPotential
import UnifiedAA.ProbabilityBounds

/-! The AA statement's `Fin N` normalization and the generic finite-law API.
Keeping these definitions separate lets their bridges be checked without
loading the upstream theorem's complete Mathlib dependency graph. -/

namespace UnifiedAA

open scoped BigOperators

noncomputable def cubeEval {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    (x : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p

noncomputable def cubeMean {N : ℕ} (f : (Fin N → Bool) → ℝ) : ℝ :=
  (∑ x, f x) / 2 ^ N

noncomputable def cubeVariance {N : ℕ} (f : (Fin N → Bool) → ℝ) : ℝ :=
  cubeMean (fun x => (f x - cubeMean f) ^ 2)

noncomputable def flipInfluence {N : ℕ} (f : (Fin N → Bool) → ℝ) (i : Fin N) : ℝ :=
  cubeMean (fun x => (f x - f (Function.update x i (!x i))) ^ 2)

theorem cubeMean_eq_uniform_expect {N : ℕ} (f : (Fin N → Bool) → ℝ) :
    cubeMean f = (FiniteLaw.uniform (Fin N → Bool)).expect f := by
  rw [FiniteLaw.uniform_expect]
  simp [cubeMean, Fintype.card_fun, Fintype.card_bool]

theorem cubeVariance_eq_uniform_variance {N : ℕ} (f : (Fin N → Bool) → ℝ) :
    cubeVariance f = (FiniteLaw.uniform (Fin N → Bool)).variance f := by
  simp only [cubeVariance, cubeMean_eq_uniform_expect, FiniteLaw.variance]

theorem flipInfluence_eq_cubeFlipInfluence {N : ℕ}
    (f : (Fin N → Bool) → ℝ) (i : Fin N) :
    flipInfluence f i = cubeFlipInfluence f i := by
  simp only [flipInfluence, cubeMean_eq_uniform_expect, cubeFlipInfluence, flip]

theorem cubeEval_restrict {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    (i : Fin N) (b : Bool) :
    cubeEval (restrictPolynomial p i b) = restrictBit (cubeEval p) i b :=
  cubeEval_restrictPolynomial p i b

theorem cubeEval_totalFlipInfluence_le {N d : ℕ} (p : MvPolynomial (Fin N) ℝ)
    (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) :
    totalFlipInfluence (cubeEval p) ≤ d :=
  polynomial_totalFlipInfluence_le p degree bounded

end UnifiedAA
