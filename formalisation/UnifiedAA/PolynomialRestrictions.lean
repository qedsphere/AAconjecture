import UnifiedAA.CubeConditioning
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Polynomial restrictions and normalization bridges for scalar simulation. -/

namespace UnifiedAA

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem restrictBit_bounded (f : (I → Bool) → ℝ)
    (bounded : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (i : I) (b : Bool) :
    ∀ x, 0 ≤ restrictBit f i b x ∧ restrictBit f i b x ≤ 1 :=
  fun x => bounded _

/-- Substituting degree-one polynomials for variables cannot increase total
degree. This specializes below to fixing one variable to a constant. -/
theorem totalDegree_bind₁_le (g : I → MvPolynomial I ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial I ℝ) :
    (MvPolynomial.bind₁ g p).totalDegree ≤ p.totalDegree := by
  have hmono (m : I →₀ ℕ) (c : ℝ) :
      (MvPolynomial.bind₁ g (MvPolynomial.monomial m c)).totalDegree ≤
        m.sum (fun _ e => e) := by
    rw [MvPolynomial.bind₁_monomial]
    calc
      (MvPolynomial.C c * ∏ i ∈ m.support, g i ^ m i).totalDegree ≤
          (MvPolynomial.C c).totalDegree +
            (∏ i ∈ m.support, g i ^ m i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + ∑ i ∈ m.support, (g i ^ m i).totalDegree := by
        rw [MvPolynomial.totalDegree_C]
        exact Nat.add_le_add_left (MvPolynomial.totalDegree_finsetProd _ _) 0
      _ ≤ ∑ i ∈ m.support, m i := by
        simp only [zero_add]
        apply Finset.sum_le_sum
        intro i hi
        exact (MvPolynomial.totalDegree_pow _ _).trans
          (by simpa using Nat.mul_le_mul_left (m i) (hg i))
      _ = m.sum (fun _ e => e) := by
        rw [Finsupp.sum]
  calc
    (MvPolynomial.bind₁ g p).totalDegree =
        (MvPolynomial.bind₁ g
          (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m))).totalDegree := by
      rw [← p.as_sum]
    _ ≤ p.totalDegree := by
      rw [map_sum]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro m hm
      exact (hmono m (p.coeff m)).trans (MvPolynomial.le_totalDegree hm)

noncomputable def restrictPolynomial (p : MvPolynomial I ℝ) (i : I) (b : Bool) :
    MvPolynomial I ℝ :=
  MvPolynomial.bind₁
    (fun j => if j = i then MvPolynomial.C (if b then 1 else 0) else MvPolynomial.X j) p

theorem restrictPolynomial_degree (p : MvPolynomial I ℝ) (i : I) (b : Bool) :
    (restrictPolynomial p i b).totalDegree ≤ p.totalDegree := by
  apply totalDegree_bind₁_le
  intro j
  by_cases hji : j = i
  · subst j
    cases b <;> simp
  · simp [hji, MvPolynomial.totalDegree_X]

theorem restrictPolynomial_degree_le {p : MvPolynomial I ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (i : I) (b : Bool) :
    (restrictPolynomial p i b).totalDegree ≤ d :=
  (restrictPolynomial_degree p i b).trans hp

theorem eval_restrictPolynomial (p : MvPolynomial I ℝ) (i : I) (b : Bool)
    (x : I → ℝ) :
    MvPolynomial.eval x (restrictPolynomial p i b) =
      MvPolynomial.eval (Function.update x i (if b then 1 else 0)) p := by
  unfold restrictPolynomial MvPolynomial.eval
  rw [MvPolynomial.eval₂Hom_bind₁]
  have hh :
      MvPolynomial.eval₂Hom (RingHom.id ℝ)
          (fun j => MvPolynomial.eval₂Hom (RingHom.id ℝ) x
            (if j = i then MvPolynomial.C (if b then 1 else 0) else MvPolynomial.X j)) =
        MvPolynomial.eval₂Hom (RingHom.id ℝ)
          (Function.update x i (if b then 1 else 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, Function.update_of_ne hji]
  exact DFunLike.congr_fun hh p

theorem cubeEval_restrictPolynomial (p : MvPolynomial I ℝ) (i : I) (b : Bool) :
    (fun x => MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0)
      (restrictPolynomial p i b)) =
      restrictBit (fun x => MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) p) i b := by
  funext x
  rw [eval_restrictPolynomial]
  unfold restrictBit
  have hv : Function.update (fun j => if x j then (1 : ℝ) else 0) i
      (if b then 1 else 0) =
      (fun j => if Function.update x i b j then (1 : ℝ) else 0) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, Function.update_of_ne hji]
  rw [hv]

theorem cubeEval_restrictPolynomial_bounded (p : MvPolynomial I ℝ)
    (bounded : ∀ x : I → Bool,
      0 ≤ MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) p ≤ 1)
    (i : I) (b : Bool) :
    ∀ x : I → Bool,
      0 ≤ MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0)
        (restrictPolynomial p i b) ∧
      MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0)
        (restrictPolynomial p i b) ≤ 1 := by
  intro x
  have h := congrFun (cubeEval_restrictPolynomial p i b) x
  rw [h]
  exact bounded _

/-- Apply a finite-cube partial assignment. A coordinate mapped to `none`
remains free. -/
def applyPartialAssignment (a : I → Option Bool) (x : I → Bool) : I → Bool :=
  fun j => match a j with
    | none => x j
    | some b => b

def restrictBits (f : (I → Bool) → ℝ) (a : I → Option Bool) :
    (I → Bool) → ℝ :=
  fun x => f (applyPartialAssignment a x)

/-- Simultaneously fix every polynomial variable selected by a partial
Boolean assignment. -/
noncomputable def restrictPolynomialPartial (p : MvPolynomial I ℝ)
    (a : I → Option Bool) : MvPolynomial I ℝ :=
  MvPolynomial.bind₁
    (fun j => match a j with
      | none => MvPolynomial.X j
      | some b => MvPolynomial.C (if b then (1 : ℝ) else 0)) p

theorem restrictPolynomialPartial_degree (p : MvPolynomial I ℝ)
    (a : I → Option Bool) :
    (restrictPolynomialPartial p a).totalDegree ≤ p.totalDegree := by
  unfold restrictPolynomialPartial
  apply totalDegree_bind₁_le
  intro j
  cases h : a j with
  | none => simp [restrictPolynomialPartial, h, MvPolynomial.totalDegree_X]
  | some b => cases b <;> simp [restrictPolynomialPartial, h]

theorem eval_restrictPolynomialPartial (p : MvPolynomial I ℝ)
    (a : I → Option Bool) (x : I → ℝ) :
    MvPolynomial.eval x (restrictPolynomialPartial p a) =
      MvPolynomial.eval
        (fun j => match a j with
          | none => x j
          | some b => if b then 1 else 0) p := by
  unfold restrictPolynomialPartial MvPolynomial.eval
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply DFunLike.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    cases h : a j with
    | none => simp [h]
    | some b => cases b <;> simp [h]

theorem cubeEval_restrictPolynomialPartial (p : MvPolynomial I ℝ)
    (a : I → Option Bool) :
    (fun x => MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0)
      (restrictPolynomialPartial p a)) =
      restrictBits
        (fun x => MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) p) a := by
  funext x
  rw [eval_restrictPolynomialPartial]
  unfold restrictBits
  apply congrArg (fun y : I → ℝ => MvPolynomial.eval y p)
  funext j
  cases h : a j with
  | none => simp [applyPartialAssignment, h]
  | some b => cases b <;> simp [applyPartialAssignment, h]

theorem restrictPolynomialPartial_degree_le {p : MvPolynomial I ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (a : I → Option Bool) :
    (restrictPolynomialPartial p a).totalDegree ≤ d :=
  (restrictPolynomialPartial_degree p a).trans hp

theorem cubeEval_restrictPolynomialPartial_bounded (p : MvPolynomial I ℝ)
    (bounded : ∀ x : I → Bool,
      0 ≤ MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) p ≤ 1)
    (a : I → Option Bool) :
    ∀ x : I → Bool,
      0 ≤ MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0)
        (restrictPolynomialPartial p a) ∧
      MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0)
        (restrictPolynomialPartial p a) ≤ 1 := by
  intro x
  have h := congrFun (cubeEval_restrictPolynomialPartial p a) x
  rw [h]
  exact bounded _

end UnifiedAA
