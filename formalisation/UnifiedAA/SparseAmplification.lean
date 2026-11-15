import UnifiedAA.QuantumTablewise

/-! The sparse-witness corollary: a set of at most k valid outputs with mass
alpha supplies a heavy atom, and a single repeated extractor works tablewise. -/

namespace UnifiedAA
open QuantumQueryComplexity

def SparseValidMass {Y : Type*} (p : Y → ℝ) (valid : Y → Prop) (k : ℕ) (α : ℝ) : Prop :=
  ∃ S : Finset Y, (∀ y ∈ S, valid y) ∧ S.card ≤ k ∧ α ≤ ∑ y ∈ S, p y

theorem SparseValidMass.exists_heavy {Y : Type*} [Fintype Y] [DecidableEq Y]
    {p : Y → ℝ} {valid : Y → Prop} {k : ℕ} {α : ℝ}
    (h : SparseValidMass p valid k α) (hk : 0 < k) (hα : 0 < α) :
    ∃ y, valid y ∧ α / k ≤ p y := by
  obtain ⟨S, hvalid, hcard, hmass⟩ := h
  obtain ⟨y, hy, hheavy⟩ := exists_heavy_of_sparse_mass p S k hk α hα hcard hmass
  exact ⟨y, hvalid y hy, hheavy⟩

abbrev RepeatedAffineSeed (L : ℕ) (t η : ℝ) :=
  Fin (dyadicExponent (1 / η)) → AffineSeed L (bucketBits t)

/-- Corollary 4.2 in the native-value query model, with exact integer query
budgets. The estimator family is fixed once; repetitions use independent
affine hashes. The exceptional-set bound is delta, independently of beta. -/
theorem exists_sparse_quantum_extractor {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (hAA : AaronsonAmbainis.PrintedConjecture)
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
  classical
  let G := fun x => SparseValidMass (fun y => A.prob x q y) (valid x) k α
  have hw : ∀ x, ∃ y, G x → valid x y ∧ α / k ≤ A.prob x q y := by
    intro x
    by_cases hx : G x
    · obtain ⟨y, hy⟩ := hx.exists_heavy hk hα
      exact ⟨y, fun _ => hy⟩
    · exact ⟨fun _ => false, fun h => False.elim (hx h)⟩
  choose witness heavy using hw
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < α / (k : ℝ) := div_pos hα hk'
  have ht1 : α / (k : ℝ) ≤ 1 := (div_le_one hk').mpr (hα1.trans hk1)
  obtain ⟨extract, E, cost, sound, hE, hgood⟩ := exists_amplified_affine_extractor
    hAA A q valid G witness (α / k) δ η ht ht1 hδ hδ1 hη heavy
    verify V verifierCost verifierCorrect
  refine ⟨extract, E, cost, sound, hE, ?_, hgood⟩
  have hi := (FiniteLaw.uniform (Fin N → Bool)).prob_inter_compl_ge G E
  linarith

end UnifiedAA
