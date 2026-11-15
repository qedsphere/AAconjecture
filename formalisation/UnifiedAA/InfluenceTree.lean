import UnifiedAA.ConditionalMeans
import UnifiedAA.CubeNormalization

/-! Constructing a fresh tree from a restriction-stable influence rule.
The influence rule is a theorem parameter, to be supplied by the AA interface.
The finite construction, termination, leaf variances and cost are proved here. -/

namespace UnifiedAA

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Agreement on the remaining coordinates determines the function. -/
def CubeDependsOn (f : (I → Bool) → ℝ) (s : Finset I) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

theorem CubeDependsOn.restrict {f : (I → Bool) → ℝ} {s : Finset I}
    (hf : CubeDependsOn f s) (i : I) (b : Bool) :
    CubeDependsOn (restrictBit f i b) (s.erase i) := by
  intro x y hxy
  apply hf
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simp only [Function.update_of_ne hji]
    exact hxy j (Finset.mem_erase.mpr ⟨hji, hj⟩)

theorem CubeDependsOn.influence_zero {f : (I → Bool) → ℝ} {s : Finset I}
    (hf : CubeDependsOn f s) {i : I} (hi : i ∉ s) :
    cubeFlipInfluence f i = 0 := by
  have heq (x : I → Bool) : f x = f (flip i x) := by
    apply hf
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [flip, hji]
  unfold cubeFlipInfluence
  have hz : (fun x => (f x - f (flip i x)) ^ 2) = fun _ => (0 : ℝ) := by
    funext x
    rw [heq x, sub_self, zero_pow (by omega)]
  rw [hz, FiniteLaw.expect_const]

namespace DecisionTree

/-- An influence rule constructs a finite fresh tree, with exact conditional
means at its leaves and expected cost controlled by the initial potential. -/
theorem exists_of_influence_rule
    (P : ((I → Bool) → ℝ) → Prop) (τ γ : ℝ) (hγ : 0 < γ)
    (closed : ∀ f, P f → ∀ i b, P (restrictBit f i b))
    (choose : ∀ f, P f → τ < (FiniteLaw.uniform (I → Bool)).variance f →
      ∃ i, γ ≤ cubeFlipInfluence f i)
    (s : Finset I) (f : (I → Bool) → ℝ) (hf : P f) (hs : CubeDependsOn f s) :
    ∃ t : DecisionTree I, t.Fresh ∧ t.coordinates ⊆ s ∧
      t.HasLeafVariance τ f ∧ γ * t.expectedQueries ≤ totalFlipInfluence f := by
  classical
  induction s using Finset.strongInductionOn generalizing f with
  | _ s ih =>
    by_cases hv : (FiniteLaw.uniform (I → Bool)).variance f ≤ τ
    · refine ⟨.leaf ((FiniteLaw.uniform (I → Bool)).expect f), trivial,
        by simp [coordinates], ⟨rfl, hv⟩, ?_⟩
      simpa [expectedQueries] using totalFlipInfluence_nonneg f
    · obtain ⟨i, hi⟩ := choose f hf (lt_of_not_ge hv)
      have his : i ∈ s := by
        by_contra hn
        have hz := hs.influence_zero hn
        linarith
      have hsub : s.erase i ⊂ s := Finset.erase_ssubset his
      obtain ⟨t0, ht0, hs0, hv0, hc0⟩ :=
        ih (s.erase i) hsub (restrictBit f i false) (closed f hf i false) (hs.restrict i false)
      obtain ⟨t1, ht1, hs1, hv1, hc1⟩ :=
        ih (s.erase i) hsub (restrictBit f i true) (closed f hf i true) (hs.restrict i true)
      refine ⟨.query i ((FiniteLaw.uniform (I → Bool)).expect f) t0 t1,
        ⟨ht0, ht1, ?_, ?_⟩, ?_, ⟨hv0, hv1⟩, ?_⟩
      · intro h
        exact Finset.ne_of_mem_erase (hs0 h) rfl
      · intro h
        exact Finset.ne_of_mem_erase (hs1 h) rfl
      · intro j hj
        simp only [coordinates, Finset.mem_insert, Finset.mem_union] at hj
        rcases hj with rfl | hj | hj
        · exact his
        · exact Finset.mem_of_mem_erase (hs0 hj)
        · exact Finset.mem_of_mem_erase (hs1 hj)
      · have hdrop := totalFlipInfluence_drop f i
        simp only [expectedQueries]
        nlinarith

end DecisionTree
end UnifiedAA
