import UnifiedAA.FiniteProbability

/-!
# Probability core of heavy-valid-output extraction (Theorem 4.1)

The estimator's simultaneous error bound is an explicit hypothesis. This
module proves reconstruction and joint success, not the existence or query
complexity of the estimators. In particular, it does not assert scalar AA.
-/

namespace UnifiedAA

open scoped BigOperators

/-- Allocating exception d to each of B(L+1) fixed scalar predicates gives
the simultaneous-accuracy bound used in the extraction proof. -/
theorem simultaneous_estimate_failure_le {X B : Type*} [Fintype X] [Fintype B]
    [DecidableEq B] {L : ℕ} (μ : FiniteLaw X)
    (W wHat : X → B → ℝ) (U uHat : X → B → Fin L → ℝ) (e d : ℝ)
    (hw : ∀ b, μ.prob (fun x => ¬ |wHat x b - W x b| ≤ e) ≤ d)
    (hu : ∀ b j, μ.prob (fun x => ¬ |uHat x b j - U x b j| ≤ e) ≤ d) :
    μ.prob (fun x => ¬ ((∀ b, |wHat x b - W x b| ≤ e) ∧
      ∀ b j, |uHat x b j - U x b j| ≤ e)) ≤
      ((Fintype.card B : ℝ) * (L + 1)) * d := by
  classical
  let P : B ⊕ (B × Fin L) → X → Prop := fun i x => match i with
    | Sum.inl b => |wHat x b - W x b| ≤ e
    | Sum.inr (b, j) => |uHat x b j - U x b j| ≤ e
  have h : ∀ i, μ.prob (fun x => ¬ P i x) ≤ d := by
    intro i
    rcases i with b | ⟨b, j⟩
    · exact hw b
    · exact hu b j
  have hbound := μ.prob_not_forall_le P d h
  have heq : (fun x => ¬ ∀ i, P i x) =
      (fun x => ¬ ((∀ b, |wHat x b - W x b| ≤ e) ∧
        ∀ b j, |uHat x b j - U x b j| ≤ e)) := by
    funext x
    simp [P, Sum.forall, Prod.forall]
  rw [heq] at hbound
  have hcard : (Fintype.card (B ⊕ (B × Fin L)) : ℝ) =
      (Fintype.card B : ℝ) * (L + 1) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_add, Nat.cast_mul]
    ring
  rwa [hcard] at hbound

namespace FiniteLaw

/-- One round of extraction: a good table is isolated with probability 3/4,
and aggregate estimation failure is at most rho/4. No independence between
isolation and accuracy is needed. The table and hash sources are independent. -/
theorem extraction_event_bound {X H : Type*} [Fintype X] [Fintype H]
    (μ : FiniteLaw X) (ν : FiniteLaw H) (G : X → Prop)
    (isolated accurate success : X → H → Prop) (rho : ℝ)
    (good_mass : rho ≤ μ.prob G)
    (isolation : ∀ x, G x → 3 / 4 ≤ ν.prob (isolated x))
    (estimation : ∀ h, μ.prob (fun x => ¬ accurate x h) ≤ rho / 4)
    (reconstruction : ∀ x h, G x → isolated x h → accurate x h → success x h) :
    rho / 2 ≤ (μ.prod ν).prob (fun a => success a.1 a.2) := by
  classical
  have hcond : ∀ x, (if G x then (3 : ℝ) / 4 else 0) ≤
      ν.prob (fun h => G x ∧ isolated x h) := by
    intro x
    by_cases hx : G x
    · simpa [hx] using isolation x hx
    · simpa [hx] using ν.prob_nonneg (fun h => G x ∧ isolated x h)
  have hgood : (3 / 4 : ℝ) * μ.prob G ≤
      (μ.prod ν).prob (fun a => G a.1 ∧ isolated a.1 a.2) := by
    rw [prob_prod μ ν (fun x h => G x ∧ isolated x h)]
    calc
      _ = μ.expect (fun x => if G x then (3 : ℝ) / 4 else 0) := by
        unfold prob expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : G x <;> simp [hx]; ring
      _ ≤ _ := μ.expect_mono hcond
  have hbad : (μ.prod ν).prob (fun a => ¬ accurate a.1 a.2) ≤ rho / 4 := by
    rw [prob_prod_swap μ ν (fun x h => ¬ accurate x h),
      prob_prod ν μ (fun h x => ¬ accurate x h)]
    exact (ν.expect_mono estimation).trans_eq (ν.expect_const _)
  have hremove := (μ.prod ν).prob_inter_compl_ge
    (fun a => G a.1 ∧ isolated a.1 a.2) (fun a => ¬ accurate a.1 a.2)
  have hmono : (μ.prod ν).prob
      (fun a => (G a.1 ∧ isolated a.1 a.2) ∧ ¬ ¬ accurate a.1 a.2) ≤
      (μ.prod ν).prob (fun a => success a.1 a.2) := by
    apply prob_mono
    intro a ha
    exact reconstruction a.1 a.2 ha.1.1 ha.1.2 (not_not.mp ha.2)
  linarith

end FiniteLaw

/-- The probability conclusion of Theorem 4.1 for the actual bucket decoder,
conditional on the all-estimates error bound. The witness yStar depends only
on the table, never on the sampled hash. No verifier is needed to state list
membership; operational verification and its cost are a separate step. -/
theorem heavy_output_list_success {X H B : Type*} [Fintype X] [Fintype H]
    [DecidableEq B] {L : ℕ}
    (μ : FiniteLaw X) (ν : FiniteLaw H)
    (p : X → (Fin L → Bool) → ℝ)
    (hp : ∀ x y, 0 ≤ p x y) (psum : ∀ x, ∑ y, p x y = 1)
    (g : H → (Fin L → Bool) → B)
    (valid : X → (Fin L → Bool) → Prop) (G : X → Prop)
    (yStar : X → Fin L → Bool) (t buckets rho : ℝ)
    (ht : 0 < t) (hB : 0 < buckets) (hsize : 16 ≤ buckets * t)
    (heavy : ∀ x, G x → valid x (yStar x) ∧ t ≤ p x (yStar x))
    (good_mass : rho ≤ μ.prob G)
    (collision : ∀ y z, y ≠ z → ν.prob (fun h => g h y = g h z) ≤ 1 / buckets)
    (wHat : X → H → B → ℝ) (uHat : X → H → B → Fin L → ℝ)
    (estimate_failure : ∀ h, μ.prob (fun x => ¬
      ((∀ b, |wHat x h b - bucketMass (p x) (g h) b| ≤ t / 16) ∧
       ∀ b j, |uHat x h b j - bitMass (p x) (g h) (fun y j => y j) b j| ≤ t / 16))
      ≤ rho / 4) :
    rho / 2 ≤ (μ.prod ν).prob (fun a =>
      ∃ b, valid a.1 (fun j => decodeBit (wHat a.1 a.2 b) (uHat a.1 a.2 b j))) := by
  classical
  let accurate (x : X) (h : H) : Prop :=
    (∀ b, |wHat x h b - bucketMass (p x) (g h) b| ≤ t / 16) ∧
    ∀ b j, |uHat x h b j - bitMass (p x) (g h) (fun y j => y j) b j| ≤ t / 16
  let isolated (x : X) (h : H) : Prop :=
    contamination (p x) (g h) (yStar x) ≤ t / 4
  apply FiniteLaw.extraction_event_bound μ ν G isolated accurate
    (fun x h => ∃ b, valid x (fun j => decodeBit (wHat x h b) (uHat x h b j)))
    rho good_mass
  · intro x _
    have hfail := isolation_failure_le_quarter (p x) (hp x) (psum x) ν g
      (yStar x) t buckets ht hB hsize (fun y hy => collision y (yStar x) hy)
    have hn := ν.prob_not (fun h => t / 4 < contamination (p x) (g h) (yStar x))
    have hi : ν.prob (isolated x) =
        ν.prob (fun h => ¬ t / 4 < contamination (p x) (g h) (yStar x)) := by
      congr 1
      funext h
      exact propext (not_lt.symm)
    linarith
  · exact estimate_failure
  · intro x h hx hiso hacc
    refine ⟨g h (yStar x), ?_⟩
    have hdecode := decodeString_correct (p x) (hp x) (g h) (yStar x) t
      (wHat x h (g h (yStar x))) (uHat x h (g h (yStar x))) ht (heavy x hx).2
      hiso (hacc.1 _) (hacc.2 _)
    rw [hdecode]
    exact (heavy x hx).1

end UnifiedAA
