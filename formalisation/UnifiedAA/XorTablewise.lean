import UnifiedAA.XorExtraction
import UnifiedAA.SparseAmplification

/-! Tablewise and sparse-witness extraction for padded Boolean XOR queries.
The checked XOR bucket estimators are chosen once before table sampling;
independent affine seeds amplify that same family on every nonexceptional
good table. Query budgets and exceptional-set bounds match the native-value
construction exactly. -/

namespace UnifiedAA
open QuantumQueryComplexity

variable {N L : ℕ} {W B H : Type} [Fintype W] [DecidableEq W]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype H]

theorem exists_xor_tablewise_extractor
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (ν : FiniteLaw H) (g : H → (Fin L → Bool) → B)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t δ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : 16 ≤ (Fintype.card B : ℝ) * t)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ xorProb A x q (yStar x))
    (collision : ∀ y z, y ≠ z → ν.prob (fun h => g h y = g h z) ≤
      1 / (Fintype.card B : ℝ))
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ (extract : H → QueryProgram (Fin N) (Option (Fin L → Bool)))
      (E : (Fin N → Bool) → Prop),
      (∀ h x, (extract h).queries x ≤ extractorQueryBudget q L (Fintype.card B) V t δ) ∧
      (∀ h x y, (extract h).eval x = some y → valid x y) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob E ≤ δ ∧
      ∀ x, G x → ¬ E x → 1 / 2 ≤ ν.prob (fun h =>
        ∃ y, (extract h).eval x = some y ∧ valid x y) := by
  classical
  let c : ℝ := (Fintype.card B : ℝ) * (L + 1)
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hc : 0 < c := mul_pos hB (by positivity)
  have hc1 : 1 ≤ c := by
    have hb1 : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos
    dsimp [c]
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hsmall : 0 < δ / (4 * c) := div_pos hδ (by positivity)
  have hsmall1 : δ / (4 * c) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h := fun h => exists_xor_bucket_estimators hAA A q (g h)
    (t / 16) (δ / (4 * c)) (by positivity) (by linarith) hsmall hsmall1
  choose wt ut _wcost _ucost cost error using h
  let extract := fun h => verifiedBucketDecoder (wt h) (ut h) verify
  let accurate := fun x h =>
    (∀ b, |(wt h b).eval x - bucketMass (fun y => xorProb A x q y) (g h) b| ≤ t / 16) ∧
    ∀ b j, |(ut h b j).eval x -
      bitMass (fun y => xorProb A x q y) (g h) (fun y j => y j) b j| ≤ t / 16
  let isolated := fun x h => contamination (fun y => xorProb A x q y) (g h) (yStar x) ≤ t / 4
  let success := fun x h => ∃ y, (extract h).eval x = some y ∧ valid x y
  have hiso : ∀ x, G x → 3 / 4 ≤ ν.prob (isolated x) := by
    intro x _
    have hf := isolation_failure_le_quarter (fun y => xorProb A x q y)
      (fun y => xorProb_nonneg A x q y) (xorProb_sum_eq_one A x q) ν g (yStar x)
      t (Fintype.card B) ht hB hsize (fun y hy => collision y (yStar x) hy)
    have hn := ν.prob_not (fun h => t / 4 < contamination (fun y => xorProb A x q y) (g h) (yStar x))
    have hi : (fun h => ¬ t / 4 < contamination (fun y => xorProb A x q y) (g h) (yStar x)) =
        isolated x := by funext h; exact propext not_lt
    rw [hi] at hn
    linarith
  have herr : ∀ h, (FiniteLaw.uniform (Fin N → Bool)).prob (fun x => ¬ accurate x h) ≤ δ / 4 := by
    intro h
    have hcne : c ≠ 0 := ne_of_gt hc
    have heq : c * (δ / (4 * c)) = δ / 4 := by field_simp
    exact (error h).trans_eq heq
  have hrec : ∀ x h, G x → isolated x h → accurate x h → success x h := by
    intro x h hx hiso hacc
    apply verifiedBucketDecoder_success (wt h) (ut h) verify x (valid x)
      (fun y => verifierCorrect y x)
    refine ⟨g h (yStar x), ?_⟩
    have hd := decodeString_correct (fun y => xorProb A x q y) (fun y => xorProb_nonneg A x q y)
      (g h) (yStar x) t ((wt h (g h (yStar x))).eval x)
      (fun j => (ut h (g h (yStar x)) j).eval x) ht (heavy x hx).2
      hiso (hacc.1 _) (hacc.2 _)
    rw [hd]
    exact (heavy x hx).1
  obtain ⟨E, hE, hgood⟩ := (FiniteLaw.uniform (Fin N → Bool)).exists_tablewise_extraction_set
    ν G isolated accurate success δ hiso herr hrec
  refine ⟨extract, E, ?_, ?_, hE, hgood⟩
  · intro h x
    exact queries_verifiedBucketDecoder_le (wt h) (ut h) verify x _ V
      (cost h x) (fun y => verifierCost y x)
  · intro h x y hy
    exact (verifierCorrect y x).mp (verifiedBucketDecoder_sound (wt h) (ut h) verify x y hy)

/-- The tablewise construction with a concrete affine seed and automatic
bucket rounding. The exceptional set does not depend on a sampled hash. -/
theorem exists_affine_xor_tablewise_extractor
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t δ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ xorProb A x q (yStar x))
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ (extract : AffineSeed L (bucketBits t) → QueryProgram (Fin N) (Option (Fin L → Bool)))
      (E : (Fin N → Bool) → Prop),
      (∀ h x, (extract h).queries x ≤ extractorQueryBudget q L (bucketCount t) V t δ) ∧
      (∀ h x y, (extract h).eval x = some y → valid x y) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob E ≤ δ ∧
      ∀ x, G x → ¬ E x → 1 / 2 ≤ (affineHashLaw (Fin L) (bucketBits t)).prob
        (fun h => ∃ y, (extract h).eval x = some y ∧ valid x y) := by
  have hc : Fintype.card (Fin (bucketBits t) → Bool) = bucketCount t := by simp [bucketCount]
  have hs : 16 ≤ (Fintype.card (Fin (bucketBits t) → Bool) : ℝ) * t := by
    rw [hc]
    exact (bucketCount_spec t ht ht1).1
  have hcol : ∀ y z : Fin L → Bool, y ≠ z →
      (affineHashLaw (Fin L) (bucketBits t)).prob (fun h => affineHash h y = affineHash h z) ≤
        1 / (Fintype.card (Fin (bucketBits t) → Bool) : ℝ) := by
    intro y z hyz
    rw [uniform_affine_hash_collision _ y z hyz]
    simp
  simpa only [hc] using exists_xor_tablewise_extractor hAA A q
    (affineHashLaw (Fin L) (bucketBits t)) affineHash valid G yStar t δ
    ht ht1 hδ hδ1 hs heavy hcol verify V verifierCost verifierCorrect

/-- Independent affine seeds amplify the same fixed estimator family on
every nonexceptional good table, with the repetition factor in query cost. -/
theorem exists_amplified_affine_xor_extractor
    (hAA : AaronsonAmbainis.PrintedConjecture)
    (A : QAlg (Fin N) Bool (Fin L → Bool) W) (q : ℕ)
    (valid : (Fin N → Bool) → (Fin L → Bool) → Prop)
    (G : (Fin N → Bool) → Prop) (yStar : (Fin N → Bool) → Fin L → Bool)
    (t δ η : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ xorProb A x q (yStar x))
    (verify : (Fin L → Bool) → QueryProgram (Fin N) Bool) (V : ℕ)
    (verifierCost : ∀ y x, (verify y).queries x ≤ V)
    (verifierCorrect : ∀ y x, (verify y).eval x = true ↔ valid x y) :
    ∃ (extract : (Fin (dyadicExponent (1 / η)) → AffineSeed L (bucketBits t)) →
        QueryProgram (Fin N) (Option (Fin L → Bool))) (E : (Fin N → Bool) → Prop),
      (∀ seeds x, (extract seeds).queries x ≤ dyadicExponent (1 / η) *
        extractorQueryBudget q L (bucketCount t) V t δ) ∧
      (∀ seeds x y, (extract seeds).eval x = some y → valid x y) ∧
      (FiniteLaw.uniform (Fin N → Bool)).prob E ≤ δ ∧
      ∀ x, G x → ¬ E x → 1 - η ≤
        (FiniteLaw.independent (fun _ : Fin (dyadicExponent (1 / η)) =>
          affineHashLaw (Fin L) (bucketBits t))).prob
          (fun seeds => ∃ y, (extract seeds).eval x = some y ∧ valid x y) := by
  obtain ⟨p, E, cost, sound, hE, hgood⟩ := exists_affine_xor_tablewise_extractor hAA A q
    valid G yStar t δ ht ht1 hδ hδ1 heavy verify V verifierCost verifierCorrect
  refine ⟨QueryProgram.repeatWith p, E, ?_, ?_, hE, ?_⟩
  · intro seeds x
    exact QueryProgram.queries_repeatWith_le p seeds x _ (fun h => cost h x)
  · intro seeds x y hy
    exact QueryProgram.repeatWith_sound p seeds x (valid x) (fun h a => sound h x a) y hy
  · intro x hx hEx
    exact QueryProgram.repeatWith_success_ge (affineHashLaw (Fin L) (bucketBits t)) p x
      (valid x) (fun h a => sound h x a) (hgood x hx hEx) η hη

end UnifiedAA

namespace UnifiedAA
open QuantumQueryComplexity

/-- Corollary 4.2 in the padded Boolean XOR query model, with exact integer query
budgets. The estimator family is fixed once; repetitions use independent
affine hashes. The exceptional-set bound is delta, independently of beta. -/
theorem exists_sparse_xor_extractor {N L : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (hAA : AaronsonAmbainis.PrintedConjecture)
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
  classical
  let G := fun x => SparseValidMass (fun y => xorProb A x q y) (valid x) k α
  have hw : ∀ x, ∃ y, G x → valid x y ∧ α / k ≤ xorProb A x q y := by
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
  obtain ⟨extract, E, cost, sound, hE, hgood⟩ := exists_amplified_affine_xor_extractor
    hAA A q valid G witness (α / k) δ η ht ht1 hδ hδ1 hη heavy
    verify V verifierCost verifierCorrect
  refine ⟨extract, E, cost, sound, hE, ?_, hgood⟩
  have hi := (FiniteLaw.uniform (Fin N → Bool)).prob_inter_compl_ge G E
  linarith

end UnifiedAA
