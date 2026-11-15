import UnifiedAA.QueryProgram
import UnifiedAA.TablewiseAmplification

/-! Repeating a fixed oracle program with independent seeds, stopping at the
first returned candidate, with explicit physical-query accounting. -/

namespace UnifiedAA.QueryProgram

variable {I A H : Type*}

def firstSome : List (QueryProgram I (Option A)) → QueryProgram I (Option A)
  | [] => .pure none
  | p :: rest => p.bind fun result => match result with
    | none => firstSome rest
    | some a => .pure (some a)

theorem queries_firstSome_le (ps : List (QueryProgram I (Option A)))
    (x : I → Bool) (C : ℕ) (cost : ∀ p ∈ ps, p.queries x ≤ C) :
    (firstSome ps).queries x ≤ ps.length * C := by
  induction ps with
  | nil => simp [firstSome]
  | cons p ps ih =>
      have hp := cost p (by simp)
      have hr := ih (fun q hq => cost q (List.mem_cons_of_mem p hq))
      simp only [firstSome, queries_bind, List.length_cons, Nat.add_mul, Nat.one_mul]
      cases h : p.eval x <;> simp only [queries_pure] <;> omega

theorem eval_firstSome_eq_none_iff (ps : List (QueryProgram I (Option A)))
    (x : I → Bool) : (firstSome ps).eval x = none ↔ ∀ p ∈ ps, p.eval x = none := by
  induction ps with
  | nil => simp [firstSome]
  | cons p ps ih =>
      simp only [firstSome, eval_bind]
      cases h : p.eval x <;> simp [h, ih]

theorem firstSome_origin (ps : List (QueryProgram I (Option A)))
    (x : I → Bool) (a : A) (h : (firstSome ps).eval x = some a) :
    ∃ p ∈ ps, p.eval x = some a := by
  induction ps with
  | nil => simp [firstSome] at h
  | cons p ps ih =>
      simp only [firstSome, eval_bind] at h
      cases hp : p.eval x with
      | none =>
          simp only [hp] at h
          obtain ⟨q, hq, hqa⟩ := ih h
          exact ⟨q, List.mem_cons_of_mem p hq, hqa⟩
      | some b =>
          simp only [hp, eval_pure, Option.some.injEq] at h
          subst a
          exact ⟨p, List.mem_cons_self, hp⟩

def repeatWith {r : ℕ} (p : H → QueryProgram I (Option A)) (seeds : Fin r → H) :
    QueryProgram I (Option A) := firstSome (List.ofFn (fun j => p (seeds j)))

theorem queries_repeatWith_le {r : ℕ} (p : H → QueryProgram I (Option A))
    (seeds : Fin r → H) (x : I → Bool) (C : ℕ) (cost : ∀ h, (p h).queries x ≤ C) :
    (repeatWith p seeds).queries x ≤ r * C := by
  apply (queries_firstSome_le _ x C ?_).trans_eq (by simp)
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  exact cost _

theorem repeatWith_none_iff {r : ℕ} (p : H → QueryProgram I (Option A))
    (seeds : Fin r → H) (x : I → Bool) :
    (repeatWith p seeds).eval x = none ↔ ∀ j, (p (seeds j)).eval x = none := by
  simp [repeatWith, eval_firstSome_eq_none_iff]

theorem repeatWith_sound {r : ℕ} (p : H → QueryProgram I (Option A))
    (seeds : Fin r → H) (x : I → Bool) (valid : A → Prop)
    (sound : ∀ h a, (p h).eval x = some a → valid a)
    (a : A) (ha : (repeatWith p seeds).eval x = some a) : valid a := by
  obtain ⟨q, hq, hqa⟩ := firstSome_origin _ x a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  exact sound _ _ hqa

theorem repeatWith_success_ge [Fintype H] (ν : FiniteLaw H)
    (p : H → QueryProgram I (Option A)) (x : I → Bool) (valid : A → Prop)
    (sound : ∀ h a, (p h).eval x = some a → valid a)
    (hgood : 1 / 2 ≤ ν.prob (fun h => ∃ a, (p h).eval x = some a ∧ valid a))
    (η : ℝ) (hη : 0 < η) :
    1 - η ≤ (FiniteLaw.independent (fun _ : Fin (dyadicExponent (1 / η)) => ν)).prob
      (fun seeds => ∃ a, (repeatWith p seeds).eval x = some a ∧ valid a) := by
  apply (ν.amplified_success_ge _ hgood η hη).trans
  apply FiniteLaw.prob_mono
  rintro seeds ⟨j, a, ha, _⟩
  have hn : (repeatWith p seeds).eval x ≠ none := by
    intro h
    have hj := (repeatWith_none_iff p seeds x).mp h j
    simp [ha] at hj
  cases hr : (repeatWith p seeds).eval x with
  | none => exact False.elim (hn hr)
  | some b => exact ⟨b, rfl, repeatWith_sound p seeds x valid sound b hr⟩

end UnifiedAA.QueryProgram
