import UnifiedAA.FourierPotential
import UnifiedAA.PolynomialRestrictions

/-! Polynomial degree supplies the scalar simulation's initial potential bound.
The closure proofs adapt the elementary algebra in the pinned upstream
`AaronsonAmbainis/Bridge/Algebra.lean` and `Bridge/Poly.lean` to `HasWalshDegree`.
No AA theorem or analytic assumption is needed for this bound. -/

namespace UnifiedAA

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace HasWalshDegree

theorem mono {f : (I → Bool) → ℝ} {d e : ℕ}
    (hf : HasWalshDegree f d) (hde : d ≤ e) : HasWalshDegree f e := by
  obtain ⟨c, hc, hfc⟩ := hf
  exact ⟨c, fun S hS => hc S (lt_of_le_of_lt hde hS), hfc⟩

theorem const (a : ℝ) (d : ℕ) : HasWalshDegree (fun _ : I → Bool => a) d := by
  refine ⟨fun S => if S = ∅ then a else 0, ?_, ?_⟩
  · intro S hS
    have hne : S ≠ ∅ := by intro h; subst S; simp at hS
    simp [hne]
  · intro x
    simp [ite_mul, walsh_empty]

theorem character (S : Finset I) : HasWalshDegree (walsh S) S.card := by
  refine ⟨fun T => if T = S then 1 else 0, ?_, ?_⟩
  · intro T hT
    have hne : T ≠ S := by intro h; subst T; omega
    simp [hne]
  · intro x
    simp [ite_mul]

theorem add {f g : (I → Bool) → ℝ} {d : ℕ}
    (hf : HasWalshDegree f d) (hg : HasWalshDegree g d) :
    HasWalshDegree (fun x => f x + g x) d := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun S => a S + b S, fun S hS => by simp [ha S hS, hb S hS], ?_⟩
  intro x
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← hfa x, ← hgb x]

theorem smul (r : ℝ) {f : (I → Bool) → ℝ} {d : ℕ}
    (hf : HasWalshDegree f d) : HasWalshDegree (fun x => r * f x) d := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun S => r * a S, fun S hS => by simp [ha S hS], ?_⟩
  intro x
  change r * f x = ∑ S, (r * a S) * walsh S x
  rw [hfa x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem sum {J : Type*} (s : Finset J) {F : J → (I → Bool) → ℝ} {d : ℕ}
    (h : ∀ j ∈ s, HasWalshDegree (F j) d) :
    HasWalshDegree (fun x => ∑ j ∈ s, F j x) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (I := I) 0 d
  | insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self j s)).add
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem mul {f g : (I → Bool) → ℝ} {d e : ℕ}
    (hf : HasWalshDegree f d) (hg : HasWalshDegree g e) :
    HasWalshDegree (fun x => f x * g x) (d + e) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  have heq : (fun x => f x * g x) = fun x =>
      ∑ S : Finset I, ∑ T : Finset I, (a S * b T) * walsh (symmDiff S T) x := by
    funext x
    rw [hfa x, hgb x, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    rw [← walsh_mul]
    ring
  rw [heq]
  apply sum _
  intro S _
  apply sum _
  intro T _
  by_cases hS : d < S.card
  · simpa [ha S hS] using const (I := I) 0 (d + e)
  · by_cases hT : e < T.card
    · simpa [hb T hT] using const (I := I) 0 (d + e)
    · apply smul
      apply (character _).mono
      have hcard : (symmDiff S T).card ≤ S.card + T.card := by
        apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
        intro i hi
        rcases Finset.mem_symmDiff.mp hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      omega

theorem pow {f : (I → Bool) → ℝ} {d : ℕ}
    (hf : HasWalshDegree f d) (n : ℕ) : HasWalshDegree (fun x => f x ^ n) (n * d) := by
  induction n with
  | zero => simpa using const (I := I) 1 0
  | succ n ih => simpa only [pow_succ, add_one_mul] using ih.mul hf

theorem prod {J : Type*} (s : Finset J) {F : J → (I → Bool) → ℝ} {d : J → ℕ}
    (h : ∀ j ∈ s, HasWalshDegree (F j) (d j)) :
    HasWalshDegree (fun x => ∏ j ∈ s, F j x) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (I := I) 1 0
  | insert j s hj ih =>
    simpa only [Finset.prod_insert hj, Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self j s)).mul
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem coordinate (i : I) :
    HasWalshDegree (fun x : I → Bool => if x i then (1 : ℝ) else 0) 1 := by
  have heq : (fun x : I → Bool => if x i then (1 : ℝ) else 0) =
      fun x => (1 / 2 : ℝ) + (-1 / 2) * walsh {i} x := by
    funext x
    cases hx : x i <;> norm_num [walsh, hx]
  rw [heq]
  exact (const _ 1).add ((character {i}).smul (-1 / 2))

end HasWalshDegree

/-- The 0/1 evaluation of a polynomial has Walsh degree at most its total
degree, even when the polynomial itself is not multilinear. -/
theorem polynomial_hasWalshDegree (p : MvPolynomial I ℝ) {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    HasWalshDegree
      (fun x : I → Bool => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) d := by
  have heq :
      (fun x : I → Bool => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) =
      fun x => ∑ m ∈ p.support, p.coeff m * ∏ i, (if x i then (1 : ℝ) else 0) ^ m i := by
    funext x
    exact MvPolynomial.eval_eq' _ p
  rw [heq]
  apply HasWalshDegree.sum _
  intro m hm
  apply HasWalshDegree.smul
  have hmdeg : ∑ i, m i ≤ d := by
    have h := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
    exact h.trans hp
  apply HasWalshDegree.mono _ hmdeg
  have h := HasWalshDegree.prod (univ : Finset I)
    (fun i _ => (HasWalshDegree.coordinate i).pow (m i))
  simpa only [mul_one] using h

theorem totalFlipInfluence_add_const (f : (I → Bool) → ℝ) (c : ℝ) :
    totalFlipInfluence (fun x => f x + c) = totalFlipInfluence f := by
  unfold totalFlipInfluence cubeFlipInfluence
  simp only [add_sub_add_right_eq_sub]

/-- A bounded degree-d function has total squared-flip influence at most d.
Centering at 1/2 is essential for the normalization used here. -/
theorem totalFlipInfluence_le_degree {f : (I → Bool) → ℝ} {d : ℕ}
    (hf : HasWalshDegree f d) (bounded : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    totalFlipInfluence f ≤ d := by
  have hc := hf.add (HasWalshDegree.const (-1 / 2) d)
  have he := totalFlipInfluence_le_degree_energy hc
  rw [totalFlipInfluence_add_const] at he
  have hpoint : ∀ x, (f x + (-1 / 2)) ^ 2 ≤ (1 / 4 : ℝ) := by
    intro x
    obtain ⟨h0, h1⟩ := bounded x
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have henergy := (FiniteLaw.uniform (I → Bool)).expect_mono hpoint
  rw [FiniteLaw.expect_const] at henergy
  calc
    _ ≤ 4 * d * (FiniteLaw.uniform (I → Bool)).expect
        (fun x => (f x + (-1 / 2)) ^ 2) := he
    _ ≤ 4 * d * (1 / 4) := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

theorem polynomial_totalFlipInfluence_le (p : MvPolynomial I ℝ) {d : ℕ}
    (hp : p.totalDegree ≤ d)
    (bounded : ∀ x : I → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1) :
    totalFlipInfluence
      (fun x => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) ≤ d :=
  totalFlipInfluence_le_degree (polynomial_hasWalshDegree p hp) bounded

end UnifiedAA
