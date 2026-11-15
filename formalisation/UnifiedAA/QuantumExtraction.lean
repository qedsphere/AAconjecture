import UnifiedAA.QuantumSimulation
import UnifiedAA.Extraction
import UnifiedAA.OperationalExtraction

/-! Fixed quantum output predicates provide the scalar estimators used by the
bucket decoder. The trees are chosen independently of the sampled input table.
The cost below counts running each tree; verifier composition is separate. -/

namespace UnifiedAA

open QuantumQueryComplexity

variable {N L : ℕ} {W B : Type} [Fintype W] [DecidableEq W]
  [Fintype B] [DecidableEq B]

/-- Construct all B(L+1) bucket and bit-mass estimators for a fixed hash, with
a physical query bound for each tree and for the complete collection. -/
theorem exists_quantum_bucket_estimators
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (g : (Fin L → Bool) → B) (e δ : ℝ)
    (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (wt : B → DecisionTree (Fin N)) (ut : B → Fin L → DecisionTree (Fin N)),
      (∀ b x, (wt b).queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (∀ b j x, (ut b j).queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (∀ x, (∑ b, (wt b).queries x) + (∑ b, ∑ j, (ut b j).queries x) ≤
        (Fintype.card B * (L + 1)) * scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob (fun x => ¬
        ((∀ b, |(wt b).eval x - bucketMass (fun y => A.prob x q y) g b| ≤ e) ∧
        ∀ b j, |(ut b j).eval x -
          bitMass (fun y => A.prob x q y) g (fun y j => y j) b j| ≤ e)) ≤
        ((Fintype.card B : ℝ) * (L + 1)) * δ := by
  classical
  have hw : ∀ b, ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        ¬ |t.eval x - bucketMass (fun y => A.prob x q y) g b| ≤ e) ≤ δ := by
    intro b
    obtain ⟨t, cost, error⟩ := exists_quantum_scalar_estimator hAA
      (A.postcomp (fun y => decide (g y = b))) q true e δ he he1 hδ hδ1
    refine ⟨t, cost, ?_⟩
    simpa only [quantum_bucket_probability, not_le, abs_sub_comm] using error
  have hu : ∀ b j, ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        ¬ |t.eval x - bitMass (fun y => A.prob x q y) g (fun y j => y j) b j| ≤ e) ≤ δ := by
    intro b j
    obtain ⟨t, cost, error⟩ := exists_quantum_scalar_estimator hAA
      (A.postcomp (fun y => decide (g y = b ∧ y j = true)))
      q true e δ he he1 hδ hδ1
    refine ⟨t, cost, ?_⟩
    simpa only [quantum_bit_probability, not_le, abs_sub_comm] using error
  choose wt wcost werror using hw
  choose ut ucost uerror using hu
  refine ⟨wt, ut, wcost, ucost, ?_, ?_⟩
  · intro x
    calc
      _ ≤ (∑ _b : B, scalarQueryBudget (2 * q + 1) e δ) +
          ∑ _b : B, ∑ _j : Fin L, scalarQueryBudget (2 * q + 1) e δ :=
        Nat.add_le_add (Finset.sum_le_sum (fun b _ => wcost b x))
          (Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun j _ => ucost b j x)))
      _ = _ := by simp; ring
  · exact simultaneous_estimate_failure_le _ _ _ _ _ e δ werror uerror

/-- The quantum heavy-output list theorem now has constructed, bounded-query
estimators. Hash collisions and a heavy valid witness remain explicit inputs;
the conclusion concerns a list, before operational verifier composition. -/
theorem exists_quantum_heavy_output_list {H : Type} [Fintype H] [Nonempty B]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (ν : FiniteLaw H) (g : H → (Fin L → Bool) → B)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t ρ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsize : 16 ≤ (Fintype.card B : ℝ) * t)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ A.prob x q (yStar x))
    (good_mass : ρ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob G)
    (collision : ∀ y z, y ≠ z → ν.prob (fun h => g h y = g h z) ≤
      1 / (Fintype.card B : ℝ)) :
    ∃ (wt : H → B → DecisionTree (Fin N))
      (ut : H → B → Fin L → DecisionTree (Fin N)),
      (∀ h x, (∑ b, (wt h b).queries x) + (∑ b, ∑ j, (ut h b j).queries x) ≤
        (Fintype.card B * (L + 1)) * scalarQueryBudget (2 * q + 1) (t / 16)
          (ρ / (4 * ((Fintype.card B : ℝ) * (L + 1))))) ∧
      ρ / 2 ≤ ((FiniteLaw.uniform (Fin N → Bool)).prod ν).prob (fun a =>
        ∃ b, valid a.1 (fun j => decodeBit ((wt a.2 b).eval a.1) ((ut a.2 b j).eval a.1))) := by
  classical
  let c : ℝ := (Fintype.card B : ℝ) * (L + 1)
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hc : 0 < c := mul_pos hB (by positivity)
  have hc1 : 1 ≤ c := by
    have hb1 : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos
    dsimp [c]
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hδ : 0 < ρ / (4 * c) := div_pos hρ (by positivity)
  have hδ1 : ρ / (4 * c) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h := fun h => exists_quantum_bucket_estimators hAA A q (g h)
    (t / 16) (ρ / (4 * c)) (by positivity) (by linarith) hδ hδ1
  choose wt ut _wcost _ucost cost error using h
  refine ⟨wt, ut, cost, ?_⟩
  apply heavy_output_list_success (FiniteLaw.uniform (Fin N → Bool)) ν
    (fun x y => A.prob x q y) (fun x y => A.prob_nonneg x q y)
    (fun x => A.sum_prob_eq_one x q) g valid G yStar t (Fintype.card B) ρ
    ht hB hsize heavy good_mass collision
    (fun x h b => (wt h b).eval x) (fun x h b j => (ut h b j).eval x)
  intro h
  have hcne : c ≠ 0 := ne_of_gt hc
  have heq : c * (ρ / (4 * c)) = ρ / 4 := by field_simp
  exact (error h).trans_eq heq

/-- One-round operational extraction in the native value-oracle model. The
returned classical program runs the constructed estimators, decodes buckets,
and verifies candidates, with the complete additive physical-query budget. -/
theorem exists_quantum_extractor {H : Type} [Fintype H] [Nonempty B]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (ν : FiniteLaw H) (g : H → (Fin L → Bool) → B)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t ρ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsize : 16 ≤ (Fintype.card B : ℝ) * t)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ A.prob x q (yStar x))
    (good_mass : ρ ≤ (FiniteLaw.uniform (Fin N → Bool)).prob G)
    (collision : ∀ y z, y ≠ z → ν.prob (fun h => g h y = g h z) ≤
      1 / (Fintype.card B : ℝ))
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ extract : H → QueryProgram (Fin N) (Option (Fin L → Bool)),
      (∀ h x, (extract h).queries x ≤
        (Fintype.card B * (L + 1)) * scalarQueryBudget (2 * q + 1) (t / 16)
          (ρ / (4 * ((Fintype.card B : ℝ) * (L + 1)))) + Fintype.card B * V) ∧
      ρ / 2 ≤ ((FiniteLaw.uniform (Fin N → Bool)).prod ν).prob (fun a =>
        ∃ y, (extract a.2).eval a.1 = some y ∧ valid a.1 y) := by
  obtain ⟨wt, ut, cost, success⟩ := exists_quantum_heavy_output_list hAA A q ν g
    valid G yStar t ρ ht ht1 hρ hρ1 hsize heavy good_mass collision
  refine ⟨fun h => verifiedBucketDecoder (wt h) (ut h) verify, ?_, ?_⟩
  · intro h x
    exact queries_verifiedBucketDecoder_le (wt h) (ut h) verify x _ V
      (cost h x) (fun y => verifierCost y x)
  · apply success.trans
    apply FiniteLaw.prob_mono
    intro a ha
    exact verifiedBucketDecoder_success (wt a.2) (ut a.2) verify a.1 (valid a.1)
      (fun y => verifierCorrect y a.1) ha

end UnifiedAA
