import UnifiedAA.HardSector.Equivalence
import QuantumQueryComplexity.Quantum.Algorithm

/-!
# Hard sectors: the quantum class `\mathcal Q_{n,T}` (HS1.9)

Source: `notes/ian/13_hard_sector_definitions_forward.tex`, lines 143-145 (`\mathcal Q_{n,T}`, the
acceptance functions of quantum algorithms using at most `T` coordinate queries) and Theorem
`ian:hard-sector-aa-equivalence`.

`\mathcal Q_{n,T}` is instantiated with the vendored model (`QuantumQueryComplexity`,
`Quantum/Algorithm.lean`): `QAlg (Fin n) Bool Bool W` with any finite workspace `W`, value-oracle
queries to `x : Fin n → Bool`, and acceptance function `x ↦ A.prob x q true` for a query count
`q ≤ T`. Inputs are `Fin n → Bool` (the notes' `{-1,1}^n`, relabelled).
-/

namespace UnifiedAA.HardSector

open QuantumQueryComplexity

-- LOCK BEGIN
/-- `\mathcal Q_{n,T}`: acceptance probabilities `x ↦ A.prob x q true` of quantum query
algorithms `A` on `Fin n → Bool` (any finite workspace) run for `q ≤ T` queries. -/
def QuantumClass (n T : ℕ) : Set ((Fin n → Bool) → ℝ) :=
  {Q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg (Fin n) Bool Bool W) (q : ℕ),
    q ≤ T ∧ Q = fun x => A.prob x q true}
-- LOCK END

/-- Acceptance probabilities lie in `[0,1]`. -/
theorem quantumClass_mem_unit {n T : ℕ} {Q : (Fin n → Bool) → ℝ} (hQ : Q ∈ QuantumClass n T)
    (x : Fin n → Bool) : 0 ≤ Q x ∧ Q x ≤ 1 := by
  rcases hQ with ⟨W, instW, decW, A, q, _, rfl⟩
  exact ⟨A.prob_nonneg x q true, A.prob_le_one x q true⟩

/-- Theorem `ian:hard-sector-aa-equivalence` for the quantum class, (1) ⇔ (2): full AA fails for
`μ` iff polynomially weighted hard set sectors exist at every polynomial budget. -/
theorem quantum_not_fullAA_iff_setSectorWitnesses (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)) :
    ¬ FullAA μ QuantumClass ↔ SetSectorWitnesses μ QuantumClass := by
  exact not_fullAA_iff_setSectorWitnesses
    (fun _ _ _ hQ x => quantumClass_mem_unit hQ x)

/-- Theorem `ian:hard-sector-aa-equivalence` for the quantum class, (1) ⇔ (3). -/
theorem quantum_not_fullAA_iff_smoothSectorWitnesses (μ : ∀ n : ℕ, FiniteLaw (Fin n → Bool)) :
    ¬ FullAA μ QuantumClass ↔ SmoothSectorWitnesses μ QuantumClass := by
  exact not_fullAA_iff_smoothSectorWitnesses
    (fun _ _ _ hQ x => quantumClass_mem_unit hQ x)

end UnifiedAA.HardSector
