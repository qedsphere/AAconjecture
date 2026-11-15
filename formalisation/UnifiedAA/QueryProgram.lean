import UnifiedAA.DecisionTree
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Typed deterministic Boolean-oracle programs. Sequencing counts physical
queries, including repeated coordinates; all computation between queries is
free in the query model. -/

namespace UnifiedAA

universe u v w

inductive QueryProgram (I : Type u) (A : Type v) where
  | pure (answer : A)
  | query (coordinate : I) (zero one : QueryProgram I A)

namespace QueryProgram

variable {I : Type u} {A : Type v} {B : Type w}

def eval : QueryProgram I A → (I → Bool) → A
  | .pure a, _ => a
  | .query i zero one, x => if x i then one.eval x else zero.eval x

def queries : QueryProgram I A → (I → Bool) → ℕ
  | .pure _, _ => 0
  | .query i zero one, x => 1 + if x i then one.queries x else zero.queries x

def bind : QueryProgram I A → (A → QueryProgram I B) → QueryProgram I B
  | .pure a, f => f a
  | .query i zero one, f => .query i (zero.bind f) (one.bind f)

@[simp] theorem eval_pure (a : A) (x : I → Bool) : (pure a).eval x = a := rfl
@[simp] theorem queries_pure (a : A) (x : I → Bool) : (pure a).queries x = 0 := rfl

@[simp] theorem eval_bind (p : QueryProgram I A) (f : A → QueryProgram I B)
    (x : I → Bool) : (p.bind f).eval x = (f (p.eval x)).eval x := by
  induction p with
  | pure a => rfl
  | query i zero one ih0 ih1 => cases hx : x i <;> simp [bind, eval, hx, ih0, ih1]

/-- Adaptive sequencing adds the cost of the selected continuation. -/
@[simp] theorem queries_bind (p : QueryProgram I A) (f : A → QueryProgram I B)
    (x : I → Bool) :
    (p.bind f).queries x = p.queries x + (f (p.eval x)).queries x := by
  induction p with
  | pure a => simp [bind, queries, eval]
  | query i zero one ih0 ih1 =>
      cases hx : x i <;> simp [bind, queries, eval, hx, ih0, ih1, Nat.add_assoc]

/-- Scalar-estimation trees embed without altering either answers or cost. -/
def ofScalar : DecisionTree I → QueryProgram I ℝ
  | .leaf a => .pure a
  | .query i _ zero one => .query i (ofScalar zero) (ofScalar one)

@[simp] theorem eval_ofScalar (t : DecisionTree I) (x : I → Bool) :
    (ofScalar t).eval x = t.eval x := by
  induction t with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [ofScalar, eval, DecisionTree.eval, hx, ih0, ih1]

@[simp] theorem queries_ofScalar (t : DecisionTree I) (x : I → Bool) :
    (ofScalar t).queries x = t.queries x := by
  induction t with
  | leaf a => rfl
  | query i a zero one ih0 ih1 =>
      cases hx : x i <;> simp [ofScalar, queries, DecisionTree.queries, hx, ih0, ih1]

/-- Run a finite indexed collection and return all its answers. -/
def collect : {n : ℕ} → (Fin n → QueryProgram I A) → QueryProgram I (Fin n → A)
  | 0, _ => .pure (fun i => Fin.elim0 i)
  | _ + 1, ps => (ps 0).bind fun a =>
      (collect (fun i => ps i.succ)).bind fun rest => .pure (Fin.cons a rest)

@[simp] theorem eval_collect : ∀ {n : ℕ} (ps : Fin n → QueryProgram I A) (x : I → Bool),
    (collect ps).eval x = fun i => (ps i).eval x
  | 0, ps, x => by funext i; exact Fin.elim0 i
  | n + 1, ps, x => by
      simp only [collect, eval_bind, eval_pure, eval_collect]
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem queries_collect : ∀ {n : ℕ} (ps : Fin n → QueryProgram I A) (x : I → Bool),
    (collect ps).queries x = ∑ i, (ps i).queries x
  | 0, ps, x => by simp [collect]
  | n + 1, ps, x => by
      simp [collect, queries_collect, Fin.sum_univ_succ]

/-- Collect a family indexed by an arbitrary finite type. -/
noncomputable def collectFintype {J : Type*} [Fintype J]
    (ps : J → QueryProgram I A) : QueryProgram I (J → A) :=
  (collect (fun i => ps ((Fintype.equivFin J).symm i))).bind fun answers =>
    .pure (fun j => answers (Fintype.equivFin J j))

@[simp] theorem eval_collectFintype {J : Type*} [Fintype J]
    (ps : J → QueryProgram I A) (x : I → Bool) :
    (collectFintype ps).eval x = fun j => (ps j).eval x := by
  simp [collectFintype]

@[simp] theorem queries_collectFintype {J : Type*} [Fintype J]
    (ps : J → QueryProgram I A) (x : I → Bool) :
    (collectFintype ps).queries x = ∑ j, (ps j).queries x := by
  simp only [collectFintype, queries_bind, queries_collect, queries_pure, Nat.add_zero]
  exact (Fintype.equivFin J).symm.sum_comp (fun j => (ps j).queries x)

/-- Verify candidates in order, stopping at the first accepted candidate. -/
def verifyList (verify : A → QueryProgram I Bool) : List A → QueryProgram I (Option A)
  | [] => .pure none
  | a :: rest => (verify a).bind fun accepted =>
      if accepted then .pure (some a) else verifyList verify rest

theorem queries_verifyList_le (verify : A → QueryProgram I Bool) (ys : List A)
    (x : I → Bool) (V : ℕ) (cost : ∀ a, (verify a).queries x ≤ V) :
    (verifyList verify ys).queries x ≤ ys.length * V := by
  induction ys with
  | nil => simp [verifyList]
  | cons a ys ih =>
      simp only [verifyList, queries_bind, List.length_cons, Nat.add_mul, Nat.one_mul]
      have ha := cost a
      cases h : (verify a).eval x <;> simp only [h, Bool.false_eq_true, ↓reduceIte, queries_pure]
      · omega
      · omega

theorem eval_verifyList_eq_none_iff (verify : A → QueryProgram I Bool) (ys : List A)
    (x : I → Bool) :
    (verifyList verify ys).eval x = none ↔ ∀ a ∈ ys, (verify a).eval x = false := by
  induction ys with
  | nil => simp [verifyList]
  | cons a ys ih =>
      simp only [verifyList, eval_bind]
      cases h : (verify a).eval x <;> simp [h, ih]

/-- Any returned candidate was supplied in the list and accepted by the
oracle verifier on this same input table. -/
theorem verifyList_sound (verify : A → QueryProgram I Bool) (ys : List A)
    (x : I → Bool) (a : A) (h : (verifyList verify ys).eval x = some a) :
    a ∈ ys ∧ (verify a).eval x = true := by
  induction ys with
  | nil => simp [verifyList] at h
  | cons b ys ih =>
      simp only [verifyList, eval_bind] at h
      cases hb : (verify b).eval x with
      | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨hmem, hvalid⟩ := ih h
          exact ⟨List.mem_cons_of_mem b hmem, hvalid⟩
      | true =>
          simp only [hb, ↓reduceIte, eval_pure, Option.some.injEq] at h
          subst a
          exact ⟨List.mem_cons_self, hb⟩

end QueryProgram
end UnifiedAA
