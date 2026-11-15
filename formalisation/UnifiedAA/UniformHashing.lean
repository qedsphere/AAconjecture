import UnifiedAA.Uniform

/-! Exact pair collision for a uniformly random one-bit hash table. -/

namespace UnifiedAA

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

theorem prob_eq_expect_indicator (μ : FiniteLaw Y) (P : Y → Prop) [DecidablePred P] :
    μ.prob P = μ.expect (fun y => if P y then 1 else 0) := by
  classical
  unfold FiniteLaw.prob FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : P y <;> simp [h]

/-- Distinct inputs collide with probability exactly one half under a
uniformly random Boolean-valued function. -/
theorem uniform_bool_hash_collision (y z : Y) (hyz : y ≠ z) :
    (FiniteLaw.uniform (Y → Bool)).prob (fun h => h y = h z) = 1 / 2 := by
  classical
  rw [prob_eq_expect_indicator]
  let f0 : (Y → Bool) → ℝ := fun h => if false = h z then 1 else 0
  let f1 : (Y → Bool) → ℝ := fun h => if true = h z then 1 else 0
  have h0 : ∀ h, f0 (flip y h) = f0 h := by
    intro h
    dsimp [f0, flip]
    rw [Function.update_of_ne (Ne.symm hyz)]
  have h1 : ∀ h, f1 (flip y h) = f1 h := by
    intro h
    dsimp [f1, flip]
    rw [Function.update_of_ne (Ne.symm hyz)]
  have hbranch := uniform_expect_branch y f0 f1 h0 h1
  have hindicator :
      (fun h : Y → Bool => if h y = h z then (1 : ℝ) else 0) =
        (fun h => if h y then f1 h else f0 h) := by
    funext h
    cases hy : h y <;> cases hz : h z <;> simp [f0, f1, hy, hz]
  rw [hindicator, hbranch]
  have hsum : (fun h => f0 h + f1 h) = (fun _ => (1 : ℝ)) := by
    funext h
    cases hz : h z <;> simp [f0, f1, hz]
  have hadd := (FiniteLaw.uniform (Y → Bool)).expect_add f0 f1
  rw [hsum, FiniteLaw.expect_const] at hadd
  linarith

theorem uniform_bool_hash_collision_le (y z : Y) (hyz : y ≠ z) :
    (FiniteLaw.uniform (Y → Bool)).prob (fun h => h y = h z) ≤ 1 / 2 := by
  rw [uniform_bool_hash_collision y z hyz]

end UnifiedAA
