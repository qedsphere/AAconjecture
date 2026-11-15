import UnifiedAA.GibbsResampling

/-! Exact finite stationary histories. Their reverse uses the update schedule
in the opposite order; reversibility of an entire ordered sweep is not assumed. -/

namespace UnifiedAA.FiniteLaw
variable {X K : Type*} [Fintype X]

theorem ext_weights {μ ν : FiniteLaw X} (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ
  cases ν
  simp_all only [mk.injEq, funext_iff]

noncomputable def runResamplings (μ : FiniteLaw X) (positive : ∀ x, 0 < μ.weight x) :
    List (X → K) → FiniteLaw X → FiniteLaw X
  | [], ν => ν
  | key :: keys, ν => runResamplings μ positive keys (ν.bind (μ.resampleRow positive key))

theorem runResamplings_stationary (μ : FiniteLaw X) (positive : ∀ x, 0 < μ.weight x)
    (keys : List (X → K)) : μ.runResamplings positive keys μ = μ := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      have h : μ.bind (μ.resampleRow positive key) = μ :=
        ext_weights (μ.resample_stationary positive key)
      simpa only [runResamplings, h] using ih

noncomputable def resamplingHistoryWeight (μ : FiniteLaw X)
    (keys : ℕ → X → K) (states : ℕ → X) (n : ℕ) : ℝ :=
  μ.weight (states 0) * ∏ j ∈ Finset.range n,
    μ.resampleWeight (keys j) (states j) (states (j + 1))

/-- Pointwise equality of complete forward and reverse path densities.
Real multiplication is commutative, so the reversed factors may be indexed
by the original event number without changing their product. -/
theorem resampling_history_reverse (μ : FiniteLaw X) (keys : ℕ → X → K)
    (states : ℕ → X) (n : ℕ) :
    μ.resamplingHistoryWeight keys states n =
      μ.weight (states n) * ∏ j ∈ Finset.range n,
        μ.resampleWeight (keys j) (states (j + 1)) (states j) := by
  unfold resamplingHistoryWeight
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        _ = (μ.weight (states 0) * ∏ j ∈ Finset.range n,
              μ.resampleWeight (keys j) (states j) (states (j + 1))) *
              μ.resampleWeight (keys n) (states n) (states (n + 1)) := by ring
        _ = (μ.weight (states n) * μ.resampleWeight (keys n) (states n) (states (n + 1))) *
              ∏ j ∈ Finset.range n,
                μ.resampleWeight (keys j) (states (j + 1)) (states j) := by rw [ih]; ring
        _ = _ := by rw [μ.resample_detailed_balance (keys n)]; ring

/-- Dividing the joint history density by its positive stationary endpoint
mass gives exactly the product of reverse conditional updates. -/
theorem resampling_history_conditional (μ : FiniteLaw X)
    (positive : ∀ x, 0 < μ.weight x) (keys : ℕ → X → K)
    (states : ℕ → X) (n : ℕ) :
    μ.resamplingHistoryWeight keys states n / μ.weight (states n) =
      ∏ j ∈ Finset.range n,
        μ.resampleWeight (keys j) (states (j + 1)) (states j) := by
  rw [μ.resampling_history_reverse]
  exact mul_div_cancel_left₀ _ (ne_of_gt (positive (states n)))

end UnifiedAA.FiniteLaw
