import UnifiedAA.AffineExtraction

/-! One-round operational heavy-output extraction for padded Boolean XOR
queries. Fixed output postprocessing preserves the XOR state, so the direct
degree-2q XOR scalar theorem supplies every estimator with the same query
budget as the native-value construction. No query-model simulation or assumed
estimator-accuracy hypothesis is used. -/

namespace UnifiedAA

open QuantumQueryComplexity

variable {N : ℕ} {O W : Type} [DecidableEq O] [Fintype W] [DecidableEq W]

/-- Output probability after the specified number of padded XOR queries. -/
def xorProb (A : QAlg (Fin N) Bool O W) (x : Fin N → Bool) (q : ℕ) (o : O) : ℝ :=
  qProb A.readout (xorState A x q) o

theorem xorProb_nonneg (A : QAlg (Fin N) Bool O W) (x : Fin N → Bool) (q : ℕ) (o : O) :
    0 ≤ xorProb A x q o := qProb_nonneg _ _ _

theorem xorProb_sum_eq_one [Fintype O] (A : QAlg (Fin N) Bool O W)
    (x : Fin N → Bool) (q : ℕ) : ∑ o, xorProb A x q o = 1 :=
  sum_qProb_eq_one (xorState_isQState A x q) A.readout

/-- Changing only the final readout leaves the XOR state and query schedule unchanged. -/
@[simp] theorem xorState_postcomp {O' : Type} [DecidableEq O']
    (A : QAlg (Fin N) Bool O W) (g : O → O') (x : Fin N → Bool) (q : ℕ) :
    xorState (A.postcomp g) x q = xorState A x q := by
  induction q with
  | zero =>
      rw [xorState_zero, xorState_zero, QAlg.postcomp_step, QAlg.postcomp_init]
  | succ q ih =>
      rw [xorState_succ, xorState_succ, ih, QAlg.postcomp_step]

theorem xor_bucket_probability [Fintype O] {B : Type} [DecidableEq B]
    (A : QAlg (Fin N) Bool O W) (q : ℕ) (x : Fin N → Bool) (g : O → B) (b : B) :
    xorProb (A.postcomp (fun o => decide (g o = b))) x q true =
      bucketMass (fun o => xorProb A x q o) g b := by
  rw [xorProb, xorState_postcomp, QAlg.postcomp_readout,
    qProb_postcomp_eq A.readout (xorState A x q) (fun o => decide (g o = b)) true]
  simp [bucketMass, xorProb]

theorem xor_bit_probability {L : ℕ} {B : Type} [DecidableEq B]
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ) (x : Fin N → Bool)
    (g : (Fin L → Bool) → B) (b : B) (j : Fin L) :
    xorProb (A.postcomp (fun y => decide (g y = b ∧ y j = true))) x q true =
      bitMass (fun y => xorProb A x q y) g (fun y j => y j) b j := by
  rw [xorProb, xorState_postcomp, QAlg.postcomp_readout,
    qProb_postcomp_eq A.readout (xorState A x q) (fun y => decide (g y = b ∧ y j = true)) true]
  simp [bitMass, xorProb]

variable {L : ℕ} {B : Type} [Fintype B] [DecidableEq B]

/-- Construct all fixed bucket and bit-mass estimators directly from the XOR
scalar theorem, with individual and total physical query bounds. -/
theorem exists_xor_bucket_estimators
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
        ((∀ b, |(wt b).eval x - bucketMass (fun y => xorProb A x q y) g b| ≤ e) ∧
        ∀ b j, |(ut b j).eval x -
          bitMass (fun y => xorProb A x q y) g (fun y j => y j) b j| ≤ e)) ≤
        ((Fintype.card B : ℝ) * (L + 1)) * δ := by
  classical
  have hw : ∀ b, ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        ¬ |t.eval x - bucketMass (fun y => xorProb A x q y) g b| ≤ e) ≤ δ := by
    intro b
    obtain ⟨t, cost, error⟩ := exists_xor_scalar_estimator hAA
      (A.postcomp (fun y => decide (g y = b))) q true e δ he he1 hδ hδ1
    change (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
      e < |xorProb (A.postcomp (fun y => decide (g y = b))) x q true - t.eval x|) ≤ δ at error
    refine ⟨t, cost, ?_⟩
    simpa only [xor_bucket_probability, not_le, abs_sub_comm] using error
  have hu : ∀ b j, ∃ t : DecisionTree (Fin N),
      (∀ x, t.queries x ≤ scalarQueryBudget (2 * q + 1) e δ) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
        ¬ |t.eval x - bitMass (fun y => xorProb A x q y) g (fun y j => y j) b j| ≤ e) ≤ δ := by
    intro b j
    obtain ⟨t, cost, error⟩ := exists_xor_scalar_estimator hAA
      (A.postcomp (fun y => decide (g y = b ∧ y j = true)))
      q true e δ he he1 hδ hδ1
    change (FiniteLaw.uniform (Fin N → Bool)).prob (fun x =>
      e < |xorProb (A.postcomp (fun y => decide (g y = b ∧ y j = true))) x q true -
        t.eval x|) ≤ δ at error
    refine ⟨t, cost, ?_⟩
    simpa only [xor_bit_probability, not_le, abs_sub_comm] using error
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

/-- Heavy valid XOR outputs are recovered in a bucket list by constructed
estimators; the hash randomness is independent of the uniformly sampled table. -/
theorem exists_xor_heavy_output_list {H : Type} [Fintype H] [Nonempty B]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (ν : FiniteLaw H) (g : H → (Fin L → Bool) → B)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t ρ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsize : 16 ≤ (Fintype.card B : ℝ) * t)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ xorProb A x q (yStar x))
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
  have h := fun h => exists_xor_bucket_estimators hAA A q (g h)
    (t / 16) (ρ / (4 * c)) (by positivity) (by linarith) hδ hδ1
  choose wt ut _wcost _ucost cost error using h
  refine ⟨wt, ut, cost, ?_⟩
  apply heavy_output_list_success (FiniteLaw.uniform (Fin N → Bool)) ν
    (fun x y => xorProb A x q y) (fun x y => xorProb_nonneg A x q y)
    (fun x => xorProb_sum_eq_one A x q) g valid G yStar t (Fintype.card B) ρ
    ht hB hsize heavy good_mass collision
    (fun x h b => (wt h b).eval x) (fun x h b j => (ut h b j).eval x)
  intro h
  have hcne : c ≠ 0 := ne_of_gt hc
  have heq : c * (ρ / (4 * c)) = ρ / 4 := by field_simp
  exact (error h).trans_eq heq

/-- One-round operational extraction directly in the padded XOR model, with
the same scalar and verification budget as for native value queries. -/
theorem exists_xor_extractor {H : Type} [Fintype H] [Nonempty B]
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (ν : FiniteLaw H) (g : H → (Fin L → Bool) → B)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t ρ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsize : 16 ≤ (Fintype.card B : ℝ) * t)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ xorProb A x q (yStar x))
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
  obtain ⟨wt, ut, cost, success⟩ := exists_xor_heavy_output_list hAA A q ν g
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

/-- The padded-XOR extractor with concrete affine seeds and the least
sufficient power-of-two bucket count. Pair collisions and rounding are proved
by the existing affine family and dyadic bounds. -/
theorem exists_affine_xor_extractor
    (hAA : AaronsonAmbainis.PrintedConjecture)
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
    exists_xor_extractor hAA A q (affineHashLaw (Fin L) (bucketBits t))
      affineHash valid G yStar t ρ ht ht1 hρ hρ1 hs heavy good_mass hcol
      verify V verifierCost verifierCorrect

end UnifiedAA
