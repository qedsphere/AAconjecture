import UnifiedAA.QueryProgram

/-! Oracle programs that run the scalar estimators, decode every bucket and
verify candidates. Their evaluation and physical query counts are explicit. -/

namespace UnifiedAA

open QueryProgram

variable {I B : Type*} [Fintype B] {L : ℕ}

noncomputable def bucketDecoder (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I) : QueryProgram I (B → Fin L → Bool) :=
  let ps : B ⊕ (B × Fin L) → QueryProgram I ℝ := fun j => match j with
    | .inl b => ofScalar (wt b)
    | .inr (b, j) => ofScalar (ut b j)
  (collectFintype ps).bind fun a => .pure
    (fun b j => decodeBit (a (.inl b)) (a (.inr (b, j))))

@[simp] theorem eval_bucketDecoder (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I) (x : I → Bool) :
    (bucketDecoder wt ut).eval x = fun b j => decodeBit ((wt b).eval x) ((ut b j).eval x) := by
  simp [bucketDecoder]

@[simp] theorem queries_bucketDecoder (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I) (x : I → Bool) :
    (bucketDecoder wt ut).queries x =
      (∑ b, (wt b).queries x) + ∑ b, ∑ j, (ut b j).queries x := by
  simp [bucketDecoder, Fintype.sum_sum_type, Fintype.sum_prod_type]

noncomputable def verifiedBucketDecoder (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I)
    (verify : (Fin L → Bool) → QueryProgram I Bool) :
    QueryProgram I (Option (Fin L → Bool)) :=
  (bucketDecoder wt ut).bind fun ys =>
    verifyList verify (List.ofFn (fun i => ys ((Fintype.equivFin B).symm i)))

/-- The decoder uses exactly the scalar-query sum, then at most B verifier runs. -/
theorem queries_verifiedBucketDecoder_le (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I)
    (verify : (Fin L → Bool) → QueryProgram I Bool) (x : I → Bool)
    (C V : ℕ)
    (estimatorCost : (∑ b, (wt b).queries x) + (∑ b, ∑ j, (ut b j).queries x) ≤ C)
    (verifierCost : ∀ y, (verify y).queries x ≤ V) :
    (verifiedBucketDecoder wt ut verify).queries x ≤ C + Fintype.card B * V := by
  simp only [verifiedBucketDecoder, queries_bind, queries_bucketDecoder]
  have hv := queries_verifyList_le verify
    (List.ofFn (fun i => (bucketDecoder wt ut).eval x ((Fintype.equivFin B).symm i)))
    x V verifierCost
  simpa only [List.length_ofFn] using Nat.add_le_add estimatorCost hv

/-- A valid decoded bucket produces a verified valid output. Both stages query
the same table, so adaptively chosen candidates are covered by the verifier. -/
theorem verifiedBucketDecoder_success (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I)
    (verify : (Fin L → Bool) → QueryProgram I Bool) (x : I → Bool)
    (valid : (Fin L → Bool) → Prop)
    (verifierCorrect : ∀ y, (verify y).eval x = true ↔ valid y)
    (success : ∃ b, valid (fun j => decodeBit ((wt b).eval x) ((ut b j).eval x))) :
    ∃ y, (verifiedBucketDecoder wt ut verify).eval x = some y ∧ valid y := by
  classical
  let ys := (bucketDecoder wt ut).eval x
  let candidates := List.ofFn (fun i => ys ((Fintype.equivFin B).symm i))
  have hsome : (verifyList verify candidates).eval x ≠ none := by
    intro hn
    obtain ⟨b, hb⟩ := success
    have hmem : ys b ∈ candidates := by
      apply List.mem_ofFn.mpr
      exact ⟨Fintype.equivFin B b, by simp⟩
    have hfalse := (eval_verifyList_eq_none_iff verify candidates x).mp hn (ys b) hmem
    have htrue : (verify (ys b)).eval x = true :=
      (verifierCorrect _).mpr (by simpa [ys] using hb)
    simp [hfalse] at htrue
  cases hv : (verifyList verify candidates).eval x with
  | none => exact False.elim (hsome hv)
  | some y =>
      refine ⟨y, ?_, (verifierCorrect y).mp (verifyList_sound verify candidates x y hv).2⟩
      simpa only [verifiedBucketDecoder, eval_bind] using hv

/-- Every returned candidate is accepted by the verifier, independently of
whether the input table satisfies the heavy-output hypothesis. -/
theorem verifiedBucketDecoder_sound (wt : B → DecisionTree I)
    (ut : B → Fin L → DecisionTree I)
    (verify : (Fin L → Bool) → QueryProgram I Bool) (x : I → Bool)
    (y : Fin L → Bool) (h : (verifiedBucketDecoder wt ut verify).eval x = some y) :
    (verify y).eval x = true := by
  simp only [verifiedBucketDecoder, eval_bind] at h
  exact (verifyList_sound verify _ x y h).2

end UnifiedAA
