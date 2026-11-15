import UnifiedAA.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Finite Gibbs laws and exact conditional resampling. Detailed balance is
proved for each block; an ordered sweep is reversed in the opposite order. -/

namespace UnifiedAA
namespace FiniteLaw
variable {X Y K : Type*} [Fintype X] [Fintype Y]

def bind (μ : FiniteLaw X) (κ : X → FiniteLaw Y) : FiniteLaw Y where
  weight y := ∑ x, μ.weight x * (κ x).weight y
  nonneg y := Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) ((κ x).nonneg y))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one, μ.total]

noncomputable def fiberMass (μ : FiniteLaw X) (key : X → K) (k : K) : ℝ :=
  μ.prob (fun x => key x = k)

theorem fiberMass_pos (μ : FiniteLaw X) (positive : ∀ x, 0 < μ.weight x)
    (key : X → K) (x : X) : 0 < μ.fiberMass key (key x) := by
  classical
  have hx : μ.weight x ≤ μ.fiberMass key (key x) := by
    calc
      μ.weight x = (if key x = key x then μ.weight x else 0) := by simp
      _ ≤ ∑ y, if key y = key x then μ.weight y else 0 := by
        apply Finset.single_le_sum (s := Finset.univ)
          (f := fun y => if key y = key x then μ.weight y else 0)
        · intro y _; split_ifs <;> simp [μ.nonneg]
        · exact Finset.mem_univ x
  exact (positive x).trans_le hx

/-- The key records the coordinates that must remain fixed. -/
noncomputable def resampleWeight (μ : FiniteLaw X) (key : X → K) (x y : X) : ℝ := by
  classical
  exact if key x = key y then μ.weight y / μ.fiberMass key (key x) else 0

noncomputable def resampleRow (μ : FiniteLaw X) (positive : ∀ x, 0 < μ.weight x)
    (key : X → K) (x : X) : FiniteLaw X where
  weight := μ.resampleWeight key x
  nonneg y := by
    classical
    unfold resampleWeight
    split_ifs
    · exact div_nonneg (μ.nonneg y) (μ.fiberMass_pos positive key x).le
    · exact le_rfl
  total := by
    classical
    have heq : ∀ y, μ.resampleWeight key x y =
        (if key y = key x then μ.weight y else 0) / μ.fiberMass key (key x) := by
      intro y
      by_cases h : key x = key y <;> simp [resampleWeight, h, eq_comm]
    simp only [heq, div_eq_mul_inv, ← Finset.sum_mul]
    change μ.fiberMass key (key x) / μ.fiberMass key (key x) = 1
    exact div_self (ne_of_gt (μ.fiberMass_pos positive key x))

theorem resample_detailed_balance (μ : FiniteLaw X) (key : X → K) (x y : X) :
    μ.weight x * μ.resampleWeight key x y = μ.weight y * μ.resampleWeight key y x := by
  classical
  by_cases h : key x = key y
  · simp only [resampleWeight, h, ↓reduceIte]
    ring
  · simp [resampleWeight, h, Ne.symm h]

theorem resample_stationary (μ : FiniteLaw X) (positive : ∀ x, 0 < μ.weight x)
    (key : X → K) (y : X) :
    (μ.bind (μ.resampleRow positive key)).weight y = μ.weight y := by
  change (∑ x, μ.weight x * μ.resampleWeight key x y) = μ.weight y
  calc
    _ = ∑ x, μ.weight y * μ.resampleWeight key y x :=
      Finset.sum_congr rfl (fun x _ => μ.resample_detailed_balance key x y)
    _ = μ.weight y * ∑ x, (μ.resampleRow positive key y).weight x := by
      change (∑ x, μ.weight y * μ.resampleWeight key y x) =
        μ.weight y * ∑ x, μ.resampleWeight key y x
      rw [Finset.mul_sum]
    _ = μ.weight y := by rw [(μ.resampleRow positive key y).total, mul_one]

theorem two_resamplings_reverse (μ : FiniteLaw X) (first second : X → K) (x y z : X) :
    μ.weight x * μ.resampleWeight first x y * μ.resampleWeight second y z =
      μ.weight z * μ.resampleWeight second z y * μ.resampleWeight first y x := by
  rw [μ.resample_detailed_balance first x y]
  calc
    _ = (μ.weight y * μ.resampleWeight second y z) * μ.resampleWeight first y x := by ring
    _ = _ := by rw [μ.resample_detailed_balance second y z]

end FiniteLaw

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def gibbsPartition (β : ℝ) (energy : X → ℝ) : ℝ :=
  ∑ x, Real.exp (-β * energy x)

theorem gibbsPartition_pos (β : ℝ) (energy : X → ℝ) : 0 < gibbsPartition β energy := by
  classical
  apply Finset.sum_pos'
  · intro x _; exact (Real.exp_pos _).le
  · exact ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩

noncomputable def gibbsLaw (β : ℝ) (energy : X → ℝ) : FiniteLaw X where
  weight x := Real.exp (-β * energy x) / gibbsPartition β energy
  nonneg x := (div_pos (Real.exp_pos _) (gibbsPartition_pos β energy)).le
  total := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    change gibbsPartition β energy / gibbsPartition β energy = 1
    exact div_self (ne_of_gt (gibbsPartition_pos β energy))

theorem gibbsLaw_weight_pos (β : ℝ) (energy : X → ℝ) (x : X) :
    0 < (gibbsLaw β energy).weight x :=
  div_pos (Real.exp_pos _) (gibbsPartition_pos β energy)

theorem gibbs_resample_stationary {K : Type*} (β : ℝ) (energy : X → ℝ)
    (key : X → K) (y : X) :
    ((gibbsLaw β energy).bind
      ((gibbsLaw β energy).resampleRow (gibbsLaw_weight_pos β energy) key)).weight y =
      (gibbsLaw β energy).weight y :=
  (gibbsLaw β energy).resample_stationary (gibbsLaw_weight_pos β energy) key y

end UnifiedAA
