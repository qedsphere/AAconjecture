import AaronsonAmbainis.Conjecture

/-!
# Connection to the supplied, pinned AA formalization

This checks the interface to the upstream influence statement. The explicit
hAA parameter is intended to be instantiated with the upstream proved theorem,
AaronsonAmbainis.aaronson_ambainis. No new axiom is introduced. This module does
not derive a bounded-depth scalar estimation decision tree. Definitions use
the same Boolean flip normalization as PrintedConjecture.
-/

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

/-- Direct application of the upstream theorem using our named quantities. -/
theorem polynomial_has_influential_coordinate
    (hAA : AaronsonAmbainis.PrintedConjecture) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (epsilon : ℝ) (he : 0 < epsilon) (variance : epsilon ≤ cubeVariance (cubeEval p)) :
    ∃ i, (epsilon / (d : ℝ)) ^ 7 ≤ flipInfluence (cubeEval p) i := by
  exact hAA N d p degree bounded epsilon he variance

/-- The upstream exponent 7 also supplies the coarser variance^8/degree^12
scale used in the supplied manuscript. epsilon ≤ 1 and d ≥ 1 are explicit. -/
theorem coarse_influence_bound
    (hAA : AaronsonAmbainis.PrintedConjecture) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (hd : 1 ≤ d) (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (variance : epsilon ≤ cubeVariance (cubeEval p)) :
    ∃ i, epsilon ^ 8 / (d : ℝ) ^ 12 ≤ flipInfluence (cubeEval p) i := by
  obtain ⟨i, hi⟩ := polynomial_has_influential_coordinate hAA N d p degree bounded epsilon he variance
  refine ⟨i, le_trans ?_ hi⟩
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hepow : epsilon ^ 8 ≤ epsilon ^ 7 :=
    pow_le_pow_of_le_one (le_of_lt he) he1 (by omega)
  have hdpow : (d : ℝ) ^ 7 ≤ (d : ℝ) ^ 12 :=
    pow_le_pow_right₀ hd' (by omega)
  calc
    epsilon ^ 8 / (d : ℝ) ^ 12 ≤ epsilon ^ 7 / (d : ℝ) ^ 12 := by
      exact div_le_div_of_nonneg_right hepow (by positivity)
    _ ≤ epsilon ^ 7 / (d : ℝ) ^ 7 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdpow
    _ = (epsilon / (d : ℝ)) ^ 7 := (div_pow _ _ _).symm

end UnifiedAA
