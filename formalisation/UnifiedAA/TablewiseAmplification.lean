import UnifiedAA.ProbabilityBounds
import UnifiedAA.IndependentSampling
import UnifiedAA.DyadicRounding

/-! Exceptional-table control and amplification use one estimator family fixed
before the table is sampled. Only the independent hash is resampled. -/

namespace UnifiedAA.FiniteLaw

variable {X H : Type*} [Fintype X] [Fintype H]

/-- A joint estimation budget gives a small exceptional set of tables. On each
remaining good table, isolation and accuracy imply success at least one half. -/
theorem exists_tablewise_extraction_set (μ : FiniteLaw X) (ν : FiniteLaw H)
    (G : X → Prop) (isolated accurate success : X → H → Prop) (δ : ℝ)
    (isolation : ∀ x, G x → 3 / 4 ≤ ν.prob (isolated x))
    (estimation : ∀ h, μ.prob (fun x => ¬ accurate x h) ≤ δ / 4)
    (reconstruction : ∀ x h, G x → isolated x h → accurate x h → success x h) :
    ∃ E : X → Prop, μ.prob E ≤ δ ∧
      ∀ x, G x → ¬ E x → 1 / 2 ≤ ν.prob (success x) := by
  let E := fun x => (1 : ℝ) / 4 < ν.prob (fun h => ¬ accurate x h)
  have hjoint : (μ.prod ν).prob (fun a => ¬ accurate a.1 a.2) ≤ (1 / 4) * δ := by
    rw [prob_prod_swap μ ν (fun x h => ¬ accurate x h),
      prob_prod ν μ (fun h x => ¬ accurate x h)]
    calc
      _ ≤ ν.expect (fun _ => δ / 4) := ν.expect_mono estimation
      _ = _ := by rw [ν.expect_const]; ring
  refine ⟨E, μ.tablewise_exception_le ν (fun x h => ¬ accurate x h) (1 / 4) δ
    (by norm_num) hjoint, ?_⟩
  intro x hx hE
  have hacc : ν.prob (fun h => ¬ accurate x h) ≤ 1 / 4 := le_of_not_gt hE
  have hiso := isolation x hx
  have hremove := ν.prob_inter_compl_ge (isolated x) (fun h => ¬ accurate x h)
  have hmono : ν.prob (fun h => isolated x h ∧ ¬ ¬ accurate x h) ≤ ν.prob (success x) :=
    ν.prob_mono (fun h hh => reconstruction x h hx hh.1 (not_not.mp hh.2))
  linarith

/-- Independent repetitions of a fixed per-table experiment amplify a
one-half success guarantee. No fresh estimator choices depend on the table. -/
theorem repeated_success_ge (ν : FiniteLaw H) (success : H → Prop)
    (hgood : 1 / 2 ≤ ν.prob success) (r : ℕ) :
    1 - (1 / 2 : ℝ) ^ r ≤
      (independent (fun _ : Fin r => ν)).prob (fun seeds => ∃ j, success (seeds j)) := by
  have hpow : (1 - ν.prob success) ^ r ≤ (1 / 2 : ℝ) ^ r :=
    pow_le_pow_left₀ (sub_nonneg.mpr (ν.prob_le_one success)) (by linarith) r
  have h := ν.prob_no_success success r
  rw [prob_not] at h
  linarith

theorem amplified_success_ge (ν : FiniteLaw H) (success : H → Prop)
    (hgood : 1 / 2 ≤ ν.prob success) (η : ℝ) (hη : 0 < η) :
    1 - η ≤ (independent (fun _ : Fin (dyadicExponent (1 / η)) => ν)).prob
      (fun seeds => ∃ j, success (seeds j)) := by
  have h := repeated_success_ge ν success hgood (dyadicExponent (1 / η))
  have hround := dyadic_repetition_bound η hη
  linarith

end UnifiedAA.FiniteLaw
