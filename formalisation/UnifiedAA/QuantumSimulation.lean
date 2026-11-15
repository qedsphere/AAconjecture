import UnifiedAA.ScalarSimulation
import QuantumQueryComplexity.Quantum.PolynomialMethod
import QuantumQueryComplexity.Quantum.XorPolynomialMethod
import QuantumQueryComplexity.Quantum.Postcomp

/-! Reusing Troy Lee's operational quantum polynomial method to instantiate
the scalar simulator for both native value queries and padded Boolean XOR
queries. Each bridge uses its own exact operational semantics. -/

namespace UnifiedAA

open QuantumQueryComplexity

variable {N : ℕ} {O W : Type} [DecidableEq O] [Fintype W] [DecidableEq W]

/-- Regrouping measurement outcomes by a fixed classical map. -/
theorem qProb_postcomp_eq {H O' : Type} [Fintype H] [Fintype O] [DecidableEq O']
    (r : H → O) (ψ : H → ℂ) (g : O → O') (o' : O') :
    qProb (fun h => g (r h)) ψ o' =
      ∑ o, if g o = o' then qProb r ψ o else 0 := by
  classical
  unfold qProb
  calc
    _ = ∑ h, ∑ o, if r h = o then
        (if g o = o' then Complex.normSq (ψ h) else 0) else 0 := by simp
    _ = ∑ o, ∑ h, if r h = o then
        (if g o = o' then Complex.normSq (ψ h) else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro o _
      by_cases ho : g o = o' <;> simp [ho]

/-- A fixed bucket predicate has exactly the output distribution's bucket mass
and uses the original algorithm's same state and query schedule. -/
theorem quantum_bucket_probability [Fintype O] {B : Type} [DecidableEq B]
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (x : Fin N → Bool) (g : O → B) (b : B) :
    (A.postcomp (fun o => decide (g o = b))).prob x q true =
      bucketMass (fun o => A.prob x q o) g b := by
  rw [QAlg.prob, QAlg.postcomp_state, QAlg.postcomp_readout,
    qProb_postcomp_eq A.readout (A.state x q) (fun o => decide (g o = b)) true]
  simp [bucketMass, QAlg.prob]

theorem quantum_bit_probability {L : ℕ} {B : Type} [DecidableEq B]
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ) (x : Fin N → Bool)
    (g : (Fin L → Bool) → B) (b : B) (j : Fin L) :
    (A.postcomp (fun y => decide (g y = b ∧ y j = true))).prob x q true =
      bitMass (fun y => A.prob x q y) g (fun y j => y j) b j := by
  rw [QAlg.prob, QAlg.postcomp_state, QAlg.postcomp_readout,
    qProb_postcomp_eq A.readout (A.state x q) (fun y => decide (g y = b ∧ y j = true)) true]
  simp [bitMass, QAlg.prob]

/-- The acceptance polynomial and its range follow from the quantum algorithm's
semantics, using the imported polynomial method and probability bounds. -/
theorem quantum_acceptance_polynomial (A : QAlg (Fin N) Bool O W) (q : ℕ) (o : O) :
    ∃ p : MvPolynomial (Fin N) ℝ, p.totalDegree ≤ 2 * q ∧
      (∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) ∧
      ∀ x, cubeEval p x = A.prob x q o := by
  obtain ⟨p, degree, heval⟩ := A.exists_probability_polynomial q o
  have heq : ∀ x, cubeEval p x = A.prob x q o := heval
  refine ⟨p, degree, ?_, heq⟩
  intro x
  rw [heq]
  exact ⟨A.prob_nonneg x q o, A.prob_le_one' x q o⟩

/-- A q-query quantum acceptance probability has a deterministic classical
estimator, conditional only on the imported AA statement. The degree slack
`2*q+1` covers q=0 with the same positive-budget formula. -/
theorem exists_quantum_scalar_estimator
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (o : O)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |A.prob x q o - t.eval x|) ≤ δ := by
  obtain ⟨p, degree, bounded, heval⟩ := quantum_acceptance_polynomial A q o
  obtain ⟨t, cost, error⟩ := exists_aa_scalar_estimator_explicit hAA
    (d := 2 * q + 1) (by omega) p (degree.trans (by omega)) bounded e δ he he1 hδ hδ1
  exact ⟨t, cost, by simpa only [heval] using error⟩

/-- The same degree bound for the padded Boolean XOR oracle, obtained directly
from its polynomial method without a query-model simulation overhead. -/
theorem xor_acceptance_polynomial (A : QAlg (Fin N) Bool O W) (q : ℕ) (o : O) :
    ∃ p : MvPolynomial (Fin N) ℝ, p.totalDegree ≤ 2 * q ∧
      (∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) ∧
      ∀ x, cubeEval p x = qProb A.readout (xorState A x q) o := by
  obtain ⟨p, degree, heval⟩ := exists_xor_probability_polynomial A q o
  have heq : ∀ x, cubeEval p x = qProb A.readout (xorState A x q) o := heval
  refine ⟨p, degree, ?_, heq⟩
  intro x
  rw [heq]
  exact ⟨qProb_nonneg _ _ _, qProb_le_one_of_isQState (xorState_isQState A x q) o⟩

theorem exists_xor_scalar_estimator
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (o : O)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |qProb A.readout (xorState A x q) o - t.eval x|) ≤ δ := by
  obtain ⟨p, degree, bounded, heval⟩ := xor_acceptance_polynomial A q o
  obtain ⟨t, cost, error⟩ := exists_aa_scalar_estimator_explicit hAA
    (d := 2 * q + 1) (by omega) p (degree.trans (by omega)) bounded e δ he he1 hδ hδ1
  exact ⟨t, cost, by simpa only [heval] using error⟩

/-- All estimators for a fixed finite collection of output predicates can be
chosen before sampling the table. Their query counts add and their failure
probabilities obey a union bound; no independence of estimation errors is used. -/
theorem exists_quantum_predicate_estimators {J : Type*} [Fintype J]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (test : J → O → Bool)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ts : J → DecisionTree (Fin N),
      (∀ j x, (ts j).queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (∀ x, ∑ j, (ts j).queries x ≤
        Fintype.card J * scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        ∃ j, e < |(A.postcomp (test j)).prob x q true - (ts j).eval x|) ≤
        (Fintype.card J : ℝ) * δ := by
  classical
  have h := fun j => exists_quantum_scalar_estimator hAA (A.postcomp (test j))
    q true e δ he he1 hδ hδ1
  choose ts cost error using h
  refine ⟨ts, cost, ?_, ?_⟩
  · intro x
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => cost j x)
  · calc
      _ ≤ ∑ j, (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
          e < |(A.postcomp (test j)).prob x q true - (ts j).eval x|) :=
        FiniteLaw.prob_exists_le_sum _ _
      _ ≤ ∑ _j : J, δ := Finset.sum_le_sum (fun j _ => error j)
      _ = _ := by simp

end UnifiedAA
