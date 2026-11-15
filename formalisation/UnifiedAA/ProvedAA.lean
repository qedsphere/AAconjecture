import AaronsonAmbainis.Main
import UnifiedAA.SparseAmplification
import UnifiedAA.XorTablewise
import UnifiedAA.XorEntropySoundness

/-! Draft integration module: NOT YET COMPILED OR AUDITED at this checkpoint.
The full upstream Main rebuild has reached 10/74 modules.

End-to-end corollaries using the pinned, proved Aaronson--Ambainis theorem.
These declarations expose no `hAA` hypothesis. Query budgets, verifier and
classical soundness assumptions remain exactly those of the component theorems.
The upstream proof is imported, rather than asserted as a project axiom. -/

namespace UnifiedAA
open QuantumQueryComplexity

variable {N : ℕ} {O W : Type} [DecidableEq O] [Fintype W] [DecidableEq W]

theorem exists_aa_scalar_estimator_explicit_proved
    {N d : ℕ} (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (degree : p.totalDegree ≤ d)
    (bounded : ∀ x, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N), (∀ x, t.queries x ≤ scalarQueryBudget d e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |cubeEval p x - t.eval x|) ≤ δ := by
  exact exists_aa_scalar_estimator_explicit AaronsonAmbainis.aaronson_ambainis
    hd p degree bounded e δ he he1 hδ hδ1

theorem exists_quantum_scalar_estimator_proved
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (o : O)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |A.prob x q o - t.eval x|) ≤ δ := by
  exact exists_quantum_scalar_estimator AaronsonAmbainis.aaronson_ambainis
    A q o e δ he he1 hδ hδ1

theorem exists_xor_scalar_estimator_proved
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (o : O)
    (e δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob
        (fun x => e < |qProb A.readout (xorState A x q) o - t.eval x|) ≤ δ := by
  exact exists_xor_scalar_estimator AaronsonAmbainis.aaronson_ambainis
    A q o e δ he he1 hδ hδ1

theorem exists_affine_quantum_extractor_proved {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
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
  exact exists_affine_quantum_extractor AaronsonAmbainis.aaronson_ambainis
    A q valid G yStar t ρ ht ht1 hρ hρ1
    heavy good_mass verify V verifierCost verifierCorrect

theorem exists_affine_xor_extractor_proved {L : ℕ}
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t ρ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ xorProb A x q (yStar x))
    (good_mass : ρ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob G)
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ extract : AffineSeed L (bucketBits t) → QueryProgram (Fin N) (Option (Fin L → Bool)),
      (∀ h x, (extract h).queries x ≤ extractorQueryBudget q L (bucketCount t) V t ρ) ∧
      ρ / 2 ≤ ((FiniteLaw.uniform (Fin N → Bool)).prod
        (affineHashLaw (Fin L) (bucketBits t))).prob (fun a =>
          ∃ y, (extract a.2).eval a.1 = some y ∧ valid a.1 y) := by
  exact exists_affine_xor_extractor AaronsonAmbainis.aaronson_ambainis
    A q valid G yStar t ρ ht ht1 hρ hρ1
    heavy good_mass verify V verifierCost verifierCorrect

theorem accepted_entropy_exception_lt_proved {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
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
      a0 ≤ acceptedMass (fun y => A.prob x q y) (valid x) ∧
      acceptedMinEntropy (fun y => A.prob x q y) (valid x) ≤ h) < δ := by
  exact accepted_entropy_exception_lt AaronsonAmbainis.aaronson_ambainis
    A q valid verify V T verifierCost
    verifierCorrect a0 h δ σ ha0 ha01 hh hδ hδ1 budget soundness hσ

theorem xor_accepted_entropy_exception_lt_proved {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
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
  exact xor_accepted_entropy_exception_lt AaronsonAmbainis.aaronson_ambainis
    A q valid verify V T verifierCost
    verifierCorrect a0 h δ σ ha0 ha01 hh hδ hδ1 budget soundness hσ

theorem exists_sparse_quantum_extractor_proved {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q k : ℕ) (hk : 0 < k)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (α β δ η : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (sparse_mass : 1 - β ≤ (FiniteLaw.uniform (Fin N → Bool)).prob
      (fun x => SparseValidMass (fun y => A.prob x q y) (valid x) k α))
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ (extract : RepeatedAffineSeed L (α / k) η →
        QueryProgram (Fin N) (Option (Fin L → Bool))) (E : (Fin N → Bool) → Prop),
      (∀ seeds x, (extract seeds).queries x ≤ dyadicExponent (1 / η) *
        extractorQueryBudget q L (bucketCount (α / k)) V (α / k) δ) ∧
      (∀ seeds x y, (extract seeds).eval x = some y → valid x y) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob E ≤ δ ∧
      1 - β - δ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        SparseValidMass (fun y => A.prob x q y) (valid x) k α ∧ ¬ E x) ∧
      ∀ x, SparseValidMass (fun y => A.prob x q y) (valid x) k α → ¬ E x →
        1 - η ≤ (FiniteLaw.independent (fun _ : Fin (dyadicExponent (1 / η)) =>
          affineHashLaw (Fin L) (bucketBits (α / k)))).prob
          (fun seeds => ∃ y, (extract seeds).eval x = some y ∧ valid x y) := by
  exact exists_sparse_quantum_extractor AaronsonAmbainis.aaronson_ambainis
    A q k hk valid α β δ η hα hα1 hδ hδ1 hη
    sparse_mass verify V verifierCost verifierCorrect

theorem exists_sparse_xor_extractor_proved {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q k : ℕ) (hk : 0 < k)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (α β δ η : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (sparse_mass : 1 - β ≤ (FiniteLaw.uniform (Fin N → Bool)).prob
      (fun x => SparseValidMass (fun y => xorProb A x q y) (valid x) k α))
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ (extract : RepeatedAffineSeed L (α / k) η →
        QueryProgram (Fin N) (Option (Fin L → Bool))) (E : (Fin N → Bool) → Prop),
      (∀ seeds x, (extract seeds).queries x ≤ dyadicExponent (1 / η) *
        extractorQueryBudget q L (bucketCount (α / k)) V (α / k) δ) ∧
      (∀ seeds x y, (extract seeds).eval x = some y → valid x y) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob E ≤ δ ∧
      1 - β - δ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        SparseValidMass (fun y => xorProb A x q y) (valid x) k α ∧ ¬ E x) ∧
      ∀ x, SparseValidMass (fun y => xorProb A x q y) (valid x) k α → ¬ E x →
        1 - η ≤ (FiniteLaw.independent (fun _ : Fin (dyadicExponent (1 / η)) =>
          affineHashLaw (Fin L) (bucketBits (α / k)))).prob
          (fun seeds => ∃ y, (extract seeds).eval x = some y ∧ valid x y) := by
  exact exists_sparse_xor_extractor AaronsonAmbainis.aaronson_ambainis
    A q k hk valid α β δ η hα hα1 hδ hδ1 hη
    sparse_mass verify V verifierCost verifierCorrect

end UnifiedAA
