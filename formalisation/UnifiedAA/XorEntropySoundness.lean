import UnifiedAA.EntropySoundness
import UnifiedAA.XorExtraction

/-! Strict accepted-output min-entropy exception bound for padded Boolean
XOR queries. The existing finite entropy layer and classical search-soundness
interface are combined with the actual affine XOR extractor. -/

namespace UnifiedAA
open QuantumQueryComplexity

/-- Low accepted min-entropy on table mass delta would give a classical
extractor with success at least delta/2, contradicting strict soundness.
Both inequalities inside the bad event are non-strict; its mass bound is strict. -/
theorem xor_accepted_entropy_exception_lt {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V T : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y)
    (a0 h δ σ : ℝ) (ha0 : 0 < a0) (ha01 : a0 ≤ 1) (hh : 0 ≤ h)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (budget : extractorQueryBudget q L (bucketCount (a0 * (2 : ℝ) ^ (-h))) V
      (a0 * (2 : ℝ) ^ (-h)) δ ≤ T)
    (soundness : ClassicalSearchSoundness valid T σ) (hσ : σ < δ / 2) :
    (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
      a0 ≤ acceptedMass (fun y => xorProb A x q y) (valid x) ∧
      acceptedMinEntropy (fun y => xorProb A x q y) (valid x) ≤ h) < δ := by
  classical
  let t := a0 * (2 : ℝ) ^ (-h)
  let G := fun x => a0 ≤ acceptedMass (fun y => xorProb A x q y) (valid x) ∧
    acceptedMinEntropy (fun y => xorProb A x q y) (valid x) ≤ h
  by_contra hn
  have hmass : δ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob G := le_of_not_gt hn
  have hw : ∀ x, ∃ y, G x → valid x y ∧ t ≤ xorProb A x q y := by
    intro x
    by_cases hx : G x
    · obtain ⟨y, hy⟩ := exists_heavy_of_accepted_entropy_le (fun y => xorProb A x q y)
        (valid x) (fun y => xorProb_nonneg A x q y) a0 h ha0 hx.1 hx.2
      exact ⟨y, fun _ => hy⟩
    · exact ⟨fun _ => false, fun h => False.elim (hx h)⟩
  choose witness heavy using hw
  obtain ⟨ht, ht1⟩ := accepted_entropy_threshold_bounds a0 h ha0 ha01 hh
  obtain ⟨p, cost, success⟩ := exists_affine_xor_extractor hAA A q valid G witness
    t δ ht ht1 hδ hδ1 heavy hmass verify V verifierCost verifierCorrect
  have hbound := soundness (AffineSeed L (bucketBits t)) (affineHashLaw (Fin L) (bucketBits t))
    p (fun seed x => (cost seed x).trans budget)
  linarith

end UnifiedAA
