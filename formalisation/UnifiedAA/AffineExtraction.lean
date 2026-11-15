import UnifiedAA.QuantumExtraction
import UnifiedAA.AffineHashing
import UnifiedAA.DyadicRounding

/-! Operational extraction with the compact affine hash family and the least
sufficient power-of-two bucket count. -/

namespace UnifiedAA
open QuantumQueryComplexity

abbrev AffineSeed (L k : ℕ) := Fin k → (Fin L → Bool) × Bool

noncomputable def extractorQueryBudget (q L B V : ℕ) (t ρ : ℝ) : ℕ :=
  (B * (L + 1)) * scalarQueryBudget (2 * q + 1) (t / 16)
    (ρ / (4 * ((B : ℝ) * (L + 1)))) + B * V

/-- One-round extraction with a concrete affine seed and full query budget.
The collision bound follows from the constructed family. -/
theorem exists_affine_quantum_extractor {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t ρ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ A.prob x q (yStar x))
    (good_mass : ρ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob G)
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ extract : AffineSeed L (bucketBits t) → QueryProgram (Fin N) (Option (Fin L → Bool)),
      (∀ h x, (extract h).queries x ≤ extractorQueryBudget q L (bucketCount t) V t ρ) ∧
      ρ / 2 ≤ ((FiniteLaw.uniform (Fin N → Bool)).prod
        (affineHashLaw (Fin L) (bucketBits t))).prob (fun a =>
          ∃ y, (extract a.2).eval a.1 = some y ∧ valid a.1 y) := by
  have hc : Fintype.card (Fin (bucketBits t) → Bool) = bucketCount t := by
    simp [bucketCount]
  have hs : 16 ≤ (Fintype.card (Fin (bucketBits t) → Bool) : ℝ) * t := by
    rw [hc]
    exact (bucketCount_spec t ht ht1).1
  have hcol : ∀ y z : Fin L → Bool, y ≠ z →
      (affineHashLaw (Fin L) (bucketBits t)).prob (fun h => affineHash h y = affineHash h z) ≤
        1 / (Fintype.card (Fin (bucketBits t) → Bool) : ℝ) := by
    intro y z hyz
    rw [uniform_affine_hash_collision _ y z hyz]
    simp
  simpa only [hc, extractorQueryBudget] using
    exists_quantum_extractor hAA A q (affineHashLaw (Fin L) (bucketBits t))
      affineHash valid G yStar t ρ ht ht1 hρ hρ1 hs heavy good_mass hcol
      verify V verifierCost verifierCorrect

end UnifiedAA
