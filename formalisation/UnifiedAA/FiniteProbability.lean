import UnifiedAA.Hashing
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite probability, avoiding measure-theoretic measurability obligations.
Weights are normalized and nonnegative; every probability theorem is unbounded
in the cardinality of the sample space, rather than a finite computational test. -/

namespace UnifiedAA

open scoped BigOperators

structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def expect (μ : FiniteLaw A) (f : A → ℝ) : ℝ := ∑ a, μ.weight a * f a

theorem expect_add (μ : FiniteLaw A) (f g : A → ℝ) :
    μ.expect (fun a => f a + g a) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_const_mul (μ : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    μ.expect (fun a => c * f a) = c * μ.expect f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_mono (μ : FiniteLaw A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (μ.nonneg a)

theorem expect_const (μ : FiniteLaw A) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.total]

noncomputable def prob (μ : FiniteLaw A) (P : A → Prop) : ℝ := by
  classical
  exact ∑ a, if P a then μ.weight a else 0

theorem prob_nonneg (μ : FiniteLaw A) (P : A → Prop) : 0 ≤ μ.prob P := by
  classical
  exact Finset.sum_nonneg fun a _ => by
    split_ifs <;> simp [μ.nonneg]

theorem prob_mono (μ : FiniteLaw A) {P Q : A → Prop} (h : ∀ a, P a → Q a) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all [μ.nonneg]

theorem prob_le_one (μ : FiniteLaw A) (P : A → Prop) : μ.prob P ≤ 1 := by
  classical
  rw [← μ.total]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> simp [μ.nonneg]

theorem prob_not (μ : FiniteLaw A) (P : A → Prop) :
    μ.prob (fun a => ¬ P a) = 1 - μ.prob P := by
  classical
  have h : μ.prob (fun a => ¬ P a) + μ.prob P = 1 := by
    unfold prob
    rw [← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : P a <;> simp [ha]
  linarith

theorem prob_union_le (μ : FiniteLaw A) (P Q : A → Prop) :
    μ.prob (fun a => P a ∨ Q a) ≤ μ.prob P + μ.prob Q := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq, μ.nonneg]

/-- Union bound for any finite collection of predicates. -/
theorem prob_exists_le_sum (μ : FiniteLaw A) {I : Type*} [Fintype I]
    (P : I → A → Prop) :
    μ.prob (fun a => ∃ i, P i a) ≤ ∑ i, μ.prob (P i) := by
  classical
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : ∃ i, P i a
  · simp only [ha, if_true]
    obtain ⟨i, hi⟩ := ha
    calc
      μ.weight a = (if P i a then μ.weight a else 0) := by simp [hi]
      _ ≤ ∑ i, if P i a then μ.weight a else 0 := by
        apply Finset.single_le_sum (s := Finset.univ)
          (f := fun i => if P i a then μ.weight a else 0)
        · intro i _; split_ifs <;> simp [μ.nonneg]
        · exact Finset.mem_univ _
  · simp only [ha, if_false]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [μ.nonneg]

theorem prob_not_forall_le (μ : FiniteLaw A) {I : Type*} [Fintype I]
    (P : I → A → Prop) (d : ℝ) (h : ∀ i, μ.prob (fun a => ¬ P i a) ≤ d) :
    μ.prob (fun a => ¬ ∀ i, P i a) ≤ (Fintype.card I : ℝ) * d := by
  classical
  have he : (fun a => ¬ ∀ i, P i a) = (fun a => ∃ i, ¬ P i a) := by
    funext a
    exact propext not_forall
  rw [he]
  calc
    _ ≤ ∑ i, μ.prob (fun a => ¬ P i a) := μ.prob_exists_le_sum _
    _ ≤ ∑ _i : I, d := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

/-- Unnormalized Markov inequality, including a strict bad-event threshold. -/
theorem threshold_mul_prob_le (μ : FiniteLaw A) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) (r : ℝ) :
    r * μ.prob (fun a => r < f a) ≤ μ.expect f := by
  classical
  unfold prob expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : r < f a
  · simp only [ha, if_true]
    nlinarith [μ.nonneg a]
  · simp only [ha, if_false, mul_zero]
    exact mul_nonneg (μ.nonneg a) (hf a)

theorem prob_inter_compl_ge (μ : FiniteLaw A) (P Q : A → Prop) :
    μ.prob P - μ.prob Q ≤ μ.prob (fun a => P a ∧ ¬ Q a) := by
  classical
  have h : μ.prob P ≤ μ.prob (fun a => P a ∧ ¬ Q a) + μ.prob Q := by
    calc
      _ ≤ μ.prob (fun a => (P a ∧ ¬ Q a) ∨ Q a) :=
        μ.prob_mono fun a ha => by tauto
      _ ≤ _ := μ.prob_union_le _ _
  linarith

/-- Independent sampling; independence is encoded by multiplying the weights. -/
def prod {C : Type*} [Fintype C] (μ : FiniteLaw A) (ν : FiniteLaw C) :
    FiniteLaw (A × C) where
  weight a := μ.weight a.1 * ν.weight a.2
  nonneg a := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

theorem prob_prod (μ : FiniteLaw A) {C : Type*} [Fintype C] (ν : FiniteLaw C)
    (P : A → C → Prop) :
    (μ.prod ν).prob (fun a => P a.1 a.2) = μ.expect (fun a => ν.prob (P a)) := by
  classical
  simp only [prob, expect, prod, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> ring

theorem prob_prod_swap (μ : FiniteLaw A) {C : Type*} [Fintype C] (ν : FiniteLaw C)
    (P : A → C → Prop) :
    (μ.prod ν).prob (fun a => P a.1 a.2) = (ν.prod μ).prob (fun a => P a.2 a.1) := by
  classical
  simp only [prob, prod, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

end FiniteLaw

variable {Y B H : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq B] [Fintype H]

/-- Pair-collision control bounds expected contamination by c times the
remaining mass. This makes the required hash hypothesis explicit. -/
theorem expected_contamination_le (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (μ : FiniteLaw H) (g : H → Y → B) (yStar : Y) (c : ℝ)
    (collision : ∀ y, y ≠ yStar → μ.prob (fun h => g h y = g h yStar) ≤ c) :
    μ.expect (fun h => contamination p (g h) yStar) ≤
      c * ∑ y, if y ≠ yStar then p y else 0 := by
  classical
  unfold FiniteLaw.expect contamination
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : y ≠ yStar
  · have heq : (∑ h, μ.weight h * (if y ≠ yStar ∧ g h y = g h yStar then p y else 0)) =
        p y * μ.prob (fun h => g h y = g h yStar) := by
      unfold FiniteLaw.prob
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : g h y = g h yStar <;> simp [hy, hh, mul_comm]
    rw [heq, if_pos hy, mul_comm c]
    exact mul_le_mul_of_nonneg_left (collision y hy) (hp y)
  · simp [hy]

/-- The paper's 1/4 isolation failure bound, for any finite pair-universal
family. B need not be the least power of two: B*t ≥ 16 suffices. -/
theorem isolation_failure_le_quarter (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (psum : ∑ y, p y = 1) (μ : FiniteLaw H) (g : H → Y → B)
    (yStar : Y) (t buckets : ℝ) (ht : 0 < t) (hB : 0 < buckets)
    (hsize : 16 ≤ buckets * t)
    (collision : ∀ y, y ≠ yStar →
      μ.prob (fun h => g h y = g h yStar) ≤ 1 / buckets) :
    μ.prob (fun h => t / 4 < contamination p (g h) yStar) ≤ 1 / 4 := by
  have hrest : (∑ y, if y ≠ yStar then p y else 0) ≤ 1 := by
    rw [← psum]
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> simp [hp]
  have he := expected_contamination_le p hp μ g yStar (1 / buckets) collision
  have he' : μ.expect (fun h => contamination p (g h) yStar) ≤ 1 / buckets := by
    calc
      _ ≤ (1 / buckets) * ∑ y, if y ≠ yStar then p y else 0 := he
      _ ≤ (1 / buckets) * 1 := mul_le_mul_of_nonneg_left hrest (by positivity)
      _ = _ := mul_one _
  have hm := μ.threshold_mul_prob_le (fun h => contamination p (g h) yStar)
    (fun h => contamination_nonneg p hp (g h) yStar) (t / 4)
  have hc : 1 / buckets ≤ t / 16 := (div_le_iff₀ hB).2 (by nlinarith)
  nlinarith

end UnifiedAA
