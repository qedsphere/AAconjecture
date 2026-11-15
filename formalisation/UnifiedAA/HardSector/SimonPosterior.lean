import UnifiedAA.HardSector.SimonLaw

/-!
# Simon law: the posterior of the mask given a whole-label transcript (HS3.2)

Source: `notes/ian/30_simon_sector.tex`, Lemma `ian:simon-adaptive-posterior`, the
per-transcript part of its proof (lines 177-209 and 227-238).

A whole-label transcript is a finset `S` of distinct queried arguments together with their
labels `z : G → G` (only `z` on `S` matters). Its cell is the set of tables whose labels at
`S` are `z`. With `E_τ = {x + y : x ≠ y ∈ S}`:
* collision-free (`z` injective on `S`): the posterior mask is exactly uniform on
  `(G ∖ {0}) ∖ E_τ`, and `|E[Y | cell] − ρ_m| ≤ e/(N − e)` with `e = |E_τ|`, `N = M − 1`;
* a collision `z x = z y`, `x ≠ y` forces the mask `x + y`.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- The label `f(x)` read off a table `X` (coordinates `(j, x)` for `j : Fin m`). -/
def simonLabel (m : ℕ) (X : Fin (m * 2 ^ m) → Bool) (x : SimonGroup m) : SimonGroup m :=
  fun j => if X ((simonCoord m).symm (j, x)) then 1 else 0

/-- The cell of the transcript `(S, z)`: tables whose labels at the arguments in `S` are `z`. -/
def simonCell (m : ℕ) (S : Finset (SimonGroup m)) (z : SimonGroup m → SimonGroup m) :
    Set (Fin (m * 2 ^ m) → Bool) :=
  {X | ∀ x ∈ S, simonLabel m X x = z x}

/-- `E_τ = {x + y : x, y ∈ S, x ≠ y}`. -/
def simonDiffs {m : ℕ} (S : Finset (SimonGroup m)) : Finset (SimonGroup m) :=
  ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).image (fun p => p.1 + p.2)

/-- Masks still possible after a collision-free transcript: `(G ∖ {0}) ∖ E_τ`. -/
def simonLiveMasks {m : ℕ} (S : Finset (SimonGroup m)) : Finset (SimonGroup m) :=
  Finset.univ.filter (fun u => u ≠ 0 ∧ u ∉ simonDiffs S)
-- LOCK END

open scoped Classical

private lemma posterior_bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma posterior_twice {m : ℕ} (x u : SimonGroup m) : x + u + u = x := by
  funext j
  change x j + u j + u j = x j
  rw [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

/-- Representatives for the pairs are the vectors with a chosen bit zero. -/
private abbrev PosteriorRep (m : ℕ) (i : Fin m) := {x : SimonGroup m // x i = 0}

private def posteriorRep {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x : SimonGroup m) : PosteriorRep m i :=
  ⟨if x i = 0 then x else x + u, by
    split_ifs with h
    · exact h
    · have hx := (posterior_bit_cases (x i)).resolve_left h
      simp [hx, hi]; decide⟩

private lemma posteriorRep_of_zero {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x : PosteriorRep m i) : posteriorRep u i hi x = x := by
  apply Subtype.ext
  simp [posteriorRep, x.property]

private lemma posteriorRep_add {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x : SimonGroup m) : posteriorRep u i hi (x + u) = posteriorRep u i hi x := by
  apply Subtype.ext
  have htwo : (1 + 1 : ZMod 2) = 0 := rfl
  rcases posterior_bit_cases (x i) with hx | hx <;>
    simp [posteriorRep, Pi.add_apply, hx, hi, posterior_twice, htwo]

private lemma posteriorRep_eq_iff {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x y : SimonGroup m) :
    posteriorRep u i hi x = posteriorRep u i hi y ↔ y = x ∨ y = x + u := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    dsimp [posteriorRep] at h'
    split_ifs at h' with hx hy hy
    · exact Or.inl h'.symm
    · exact Or.inr (by rw [h', posterior_twice])
    · exact Or.inr h'.symm
    · exact Or.inl (add_right_cancel h').symm
  · rintro (rfl | rfl)
    · rfl
    · exact (posteriorRep_add u i hi x).symm

private def posteriorSplit {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1) :
    SimonGroup m ≃ PosteriorRep m i × Bool where
  toFun x := (posteriorRep u i hi x, decide (x i ≠ 0))
  invFun p := if p.2 then p.1.val + u else p.1.val
  left_inv x := by
    by_cases hx : x i = 0 <;> simp [posteriorRep, hx, posterior_twice]
  right_inv p := by
    rcases p with ⟨x, b⟩
    cases b
    · simp [posteriorRep_of_zero, x.property]
    · simp [posteriorRep_add, posteriorRep_of_zero, Pi.add_apply, x.property, hi]

private lemma card_posteriorRep {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1) :
    Fintype.card (PosteriorRep m i) = 2 ^ m / 2 := by
  have hc := Fintype.card_congr (posteriorSplit u i hi)
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool] at hc
  omega

/-- Restriction to the representatives identifies admissible functions with injections. -/
private def posteriorLabelEquiv {m : ℕ} (u : SimonGroup m) (hu : u ≠ 0)
    (i : Fin m) (hi : u i = 1) :
    {f : SimonGroup m → SimonGroup m // IsSimonPair u f} ≃ (PosteriorRep m i ↪ SimonGroup m) where
  toFun f := ⟨fun x => f.val x.val, by
    intro x y h
    apply Subtype.ext
    rcases (f.property.2 x y).1 h with hxy | hxy
    · exact hxy.symm
    · have he := congrFun hxy i
      simp [Pi.add_apply, x.property, y.property, hi] at he⟩
  invFun e := ⟨fun x => e (posteriorRep u i hi x), hu, by
    intro x y
    rw [e.injective.eq_iff, posteriorRep_eq_iff]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    apply (f.property.2 _ _).2
    dsimp [posteriorRep]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (by rw [posterior_twice])
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    exact congrArg e (posteriorRep_of_zero u i hi x)

/-- An injection with prescribed values is freely chosen on the two complements. -/
private noncomputable def extensionEquiv {A B C : Type*}
    (a : C ↪ A) (b : C ↪ B) :
    {e : A ↪ B // ∀ c, e (a c) = b c} ≃
      ({x : A // x ∉ Set.range a} ↪ {y : B // y ∉ Set.range b}) := by
  classical
  let ai := Equiv.ofInjective a a.injective
  let extend := fun (e : {x : A // x ∉ Set.range a} ↪
      {y : B // y ∉ Set.range b}) (x : A) =>
    if hx : x ∈ Set.range a then b (ai.symm ⟨x, hx⟩) else (e ⟨x, hx⟩).val
  have extend_a (e) (c : C) : extend e (a c) = b c := by
    change (if hx : a c ∈ Set.range a then b (ai.symm ⟨a c, hx⟩) else _) = b c
    rw [dif_pos ⟨c, rfl⟩]
    exact congrArg b (ai.symm_apply_apply c)
  have extend_out (e) (x : {x : A // x ∉ Set.range a}) :
      extend e x = (e x).val := dif_neg x.property
  have extend_inj (e) : Function.Injective (extend e) := by
    intro x y h
    by_cases hx : x ∈ Set.range a <;> by_cases hy : y ∈ Set.range a
    · simp only [extend, dif_pos hx, dif_pos hy] at h
      have he := congrArg (fun c => a c) (b.injective h)
      simpa [ai] using he
    · obtain ⟨c, rfl⟩ := hx
      rw [extend_a, extend_out e ⟨y, hy⟩] at h
      exact ((e ⟨y, hy⟩).property ⟨c, h⟩).elim
    · obtain ⟨c, rfl⟩ := hy
      rw [extend_a, extend_out e ⟨x, hx⟩] at h
      exact ((e ⟨x, hx⟩).property ⟨c, h.symm⟩).elim
    · rw [extend_out e ⟨x, hx⟩, extend_out e ⟨y, hy⟩] at h
      exact congrArg Subtype.val (e.injective (Subtype.ext h))
  refine
    { toFun := fun e => ⟨fun x => ⟨e.val x, ?_⟩, ?_⟩
      invFun := fun e => ⟨⟨extend e, extend_inj e⟩, extend_a e⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨c, hc⟩
    exact x.property ⟨c, e.val.injective ((e.property c).trans hc)⟩
  · intro x y h
    exact Subtype.ext (e.val.injective (congrArg Subtype.val h))
  · intro e
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    by_cases hx : x ∈ Set.range a
    · obtain ⟨c, rfl⟩ := hx
      exact (extend_a _ c).trans (e.property c).symm
    · exact extend_out _ ⟨x, hx⟩
  · intro e
    apply Function.Embedding.ext
    intro x
    apply Subtype.ext
    exact extend_out e x

private lemma card_extensions {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (a : C ↪ A) (b : C ↪ B) :
    Nat.card {e : A ↪ B // ∀ c, e (a c) = b c} =
      (Fintype.card B - Fintype.card C).descFactorial
        (Fintype.card A - Fintype.card C) := by
  classical
  rw [Nat.card_congr (extensionEquiv a b), Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  change (Fintype.card ↥((Set.range b)ᶜ)).descFactorial (Fintype.card ↥((Set.range a)ᶜ)) = _
  rw [Fintype.card_compl_set, Fintype.card_compl_set,
    Fintype.card_range b, Fintype.card_range a]

private lemma posterior_add_self {m : ℕ} (x : SimonGroup m) : x + x = 0 := by
  simpa using posterior_twice 0 x

private lemma posterior_sum_eq {m : ℕ} (x y u : SimonGroup m) :
    y = x + u ↔ x + y = u := by
  constructor
  · rintro rfl
    rw [← add_assoc, posterior_add_self, zero_add]
  · intro h
    rw [← h, ← add_assoc, posterior_add_self, zero_add]

private lemma mem_simonDiffs {m : ℕ} (S : Finset (SimonGroup m)) (u : SimonGroup m) :
    u ∈ simonDiffs S ↔ ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ x + y = u := by
  simp only [simonDiffs, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Prod.exists]
  aesop

private lemma zero_not_mem_simonDiffs {m : ℕ} (S : Finset (SimonGroup m)) :
    0 ∉ simonDiffs S := by
  rintro h
  obtain ⟨x, hx, y, hy, hxy, he⟩ := (mem_simonDiffs S 0).mp h
  exact hxy (by simpa using ((posterior_sum_eq x y 0).mpr he).symm)

/-- The labels of the table of `f` are the values of `f`. -/
theorem simonLabel_simonTable {m : ℕ} (f : SimonGroup m → SimonGroup m) (x : SimonGroup m) :
    simonLabel m (simonTable f) x = f x := by
  funext j
  rcases posterior_bit_cases (f x j) with h | h <;>
    simp [simonLabel, simonTable, h]

/-- Proof of Lemma `ian:simon-adaptive-posterior`: for a nonzero mask `u` and distinct labels
`z` on `S`, the number of admissible labellings compatible with the transcript is `0` if
`u ∈ E_τ` and `(M - |S|)_{M/2 - |S|}` otherwise (independent of `u` and of the labels). -/
theorem card_compatible_labellings {m : ℕ} (hm : 2 ≤ m) {u : SimonGroup m} (hu : u ≠ 0)
    {S : Finset (SimonGroup m)} {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S) :
    ((simonPairs m).filter (fun p => p.1 = u ∧ ∀ x ∈ S, p.2 x = z x)).card =
      if u ∈ simonDiffs S then 0 else (2 ^ m - S.card).descFactorial (2 ^ m / 2 - S.card) := by
  classical
  by_cases hbad : u ∈ simonDiffs S
  · rw [if_pos hbad, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hpc
    obtain ⟨x, hx, y, hy, hxy, he⟩ := (mem_simonDiffs S u).mp hbad
    have hp' : IsSimonPair u p.2 := hpc.1 ▸ (Finset.mem_filter.mp hp).2
    have hf : p.2 x = p.2 y := (hp'.2 x y).mpr (Or.inr ((posterior_sum_eq x y u).mpr he))
    exact hxy (hz hx hy (by rw [← hpc.2 x hx, ← hpc.2 y hy]; exact hf))
  · rw [if_neg hbad]
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      apply hu
      ext i
      simpa using not_exists.mp h i
    have hi' := (posterior_bit_cases (u i)).resolve_left hi
    let a : S ↪ PosteriorRep m i := ⟨fun x => posteriorRep u i hi' x, by
      intro x y he
      apply Subtype.ext
      rcases (posteriorRep_eq_iff u i hi' x y).mp he with h | h
      · exact h.symm
      · by_contra hne
        exact hbad ((mem_simonDiffs S u).mpr
          ⟨x, x.property, y, y.property, hne, (posterior_sum_eq _ _ _).mp h⟩)⟩
    let b : S ↪ SimonGroup m := ⟨fun x => z x, fun x y h => Subtype.ext (hz x.property y.property h)⟩
    have hrep (f : {f : SimonGroup m → SimonGroup m // IsSimonPair u f}) (x) :
        f.val (posteriorRep u i hi' x).val = f.val x := by
      apply (f.property.2 _ _).mpr
      dsimp [posteriorRep]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (posterior_twice x u).symm
    have hc : ((simonPairs m).filter (fun p => p.1 = u ∧ ∀ x ∈ S, p.2 x = z x)).card =
        Nat.card {f : SimonGroup m → SimonGroup m //
          IsSimonPair u f ∧ ∀ x ∈ S, f x = z x} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply Finset.card_bij (fun p _ => p.2)
      · intro p hp
        simp only [Finset.mem_filter, simonPairs, Finset.mem_univ, true_and] at hp ⊢
        exact ⟨hp.2.1 ▸ hp.1, hp.2.2⟩
      · intro p hp q hq he
        exact Prod.ext ((Finset.mem_filter.mp hp).2.1.trans
          (Finset.mem_filter.mp hq).2.1.symm) he
      · intro f hf
        refine ⟨(u, f), ?_, rfl⟩
        simpa [simonPairs] using hf
    rw [hc, ← Nat.card_congr
      (Equiv.subtypeSubtypeEquivSubtypeInter (IsSimonPair u)
        (fun f => ∀ x ∈ S, f x = z x))]
    have ec := (posteriorLabelEquiv u hu i hi').subtypeEquiv
      (p := fun f => ∀ x ∈ S, f.val x = z x)
      (q := fun e => ∀ x : S, e (a x) = b x) (by
        intro f
        change (∀ x ∈ S, f.val x = z x) ↔ ∀ x : S, f.val (posteriorRep u i hi' x).val = z x
        simp_rw [hrep]
        exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x, hx⟩⟩)
    rw [Nat.card_congr ec]
    calc
      _ = (Fintype.card (SimonGroup m) - Fintype.card S).descFactorial
          (Fintype.card (PosteriorRep m i) - Fintype.card S) := card_extensions a b
      _ = _ := by rw [card_posteriorRep u i hi']; simp [ZMod.card]

private lemma posterior_pairs_nonempty {m : ℕ} (hm : 2 ≤ m) : (simonPairs m).Nonempty := by
  classical
  let i : Fin m := ⟨0, by omega⟩
  let u : SimonGroup m := Function.update 0 i 1
  have hu : u ≠ 0 := by
    intro h
    have := congrFun h i
    simp [u] at this
  have hc := card_simonPair_fiber hm hu
  have hpos : 0 < ((simonPairs m).filter (fun p => p.1 = u)).card := by
    rw [hc]
    exact Nat.descFactorial_pos.mpr (Nat.div_le_self _ _)
  exact (Finset.card_pos.mp hpos).mono (Finset.filter_subset _ _)

private lemma posterior_expect_pushforward {A B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset A) (hS : S.Nonempty) (g : A → B) (F : B → ℝ) :
    (uniformPushforward S hS g).expect F = (∑ a ∈ S, F (g a)) / S.card := by
  classical
  unfold FiniteLaw.expect uniformPushforward
  simp only [div_eq_mul_inv, mul_right_comm _ (S.card : ℝ)⁻¹, ← Finset.sum_mul]
  congr 1
  calc
    (∑ b, ((S.filter (fun a => g a = b)).card : ℝ) * F b) =
        ∑ b, ∑ a ∈ S, if g a = b then F b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ a ∈ S, F (g a) := by
      rw [Finset.sum_comm]
      simp

/-- The counting formula also applies to arbitrary functions of the posterior mask. -/
private lemma posterior_cell_expect {m : ℕ} (hm : 2 ≤ m) {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S) (F : SimonGroup m → ℝ) :
    (simonLaw m).expect ((simonCell m S z).indicator (fun X => F (simonMask m X))) =
      (((2 ^ m - S.card).descFactorial (2 ^ m / 2 - S.card) : ℕ) : ℝ) /
        (simonPairs m).card * ∑ u ∈ simonLiveMasks S, F u := by
  classical
  rw [simonLaw, dif_pos (posterior_pairs_nonempty hm), posterior_expect_pushforward]
  have he : (∑ p ∈ simonPairs m,
      (simonCell m S z).indicator (fun X => F (simonMask m X)) (simonTable p.2)) =
      ∑ u : SimonGroup m,
        (((simonPairs m).filter (fun p => p.1 = u ∧ ∀ x ∈ S, p.2 x = z x)).card : ℝ) * F u := by
    calc
      _ = ∑ p ∈ simonPairs m, ∑ u : SimonGroup m,
          if p.1 = u ∧ (∀ x ∈ S, p.2 x = z x) then F u else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        rw [Set.indicator_apply, simonMask_simonTable hp']
        have hc : simonTable p.2 ∈ simonCell m S z ↔ ∀ x ∈ S, p.2 x = z x := by
          simp [simonCell, simonLabel_simonTable]
        simp only [hc]
        by_cases h : ∀ x ∈ S, p.2 x = z x
        · rw [if_pos h]
          simp only [and_iff_left h]
          simp
        · rw [if_neg h]
          symm
          apply Finset.sum_eq_zero
          intro u _
          exact if_neg (fun hu => h hu.2)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_filter]
        simp
  rw [he]
  have hf (u : SimonGroup m) :
      (((simonPairs m).filter (fun p => p.1 = u ∧ ∀ x ∈ S, p.2 x = z x)).card : ℝ) * F u =
        if u ∈ simonLiveMasks S then
          (((2 ^ m - S.card).descFactorial (2 ^ m / 2 - S.card) : ℕ) : ℝ) * F u else 0 := by
    by_cases hu : u = 0
    · subst u
      have hempty : (simonPairs m).filter (fun p => p.1 = 0 ∧ ∀ x ∈ S, p.2 x = z x) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp h
        exact (Finset.mem_filter.mp hp).2.1 h.1
      simp [hempty, simonLiveMasks]
    · rw [card_compatible_labellings hm hu hz]
      by_cases hd : u ∈ simonDiffs S <;> simp [simonLiveMasks, hu, hd]
  simp_rw [hf]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset (Finset.subset_univ _)]
  rw [← Finset.mul_sum]
  ring

private lemma posterior_cell_mass {m : ℕ} (hm : 2 ≤ m) {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S) :
    (simonLaw m).prob (· ∈ simonCell m S z) =
      (((2 ^ m - S.card).descFactorial (2 ^ m / 2 - S.card) : ℕ) : ℝ) /
        (simonPairs m).card * (simonLiveMasks S).card := by
  have he := posterior_cell_expect hm hz (fun _ => 1)
  simpa [FiniteLaw.expect, FiniteLaw.prob, Set.indicator_apply] using he

/-- Lemma `ian:simon-adaptive-posterior`: on a collision-free transcript the posterior mask is
exactly uniform on `(G ∖ {0}) ∖ E_τ`: for every set `B` of masks,
`μ(cell, s ∈ B) · |live| = |B ∩ live| · μ(cell)`. -/
theorem simon_posterior_uniform {m : ℕ} (hm : 2 ≤ m) {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S) (B : Finset (SimonGroup m)) :
    (simonLaw m).prob (fun X => X ∈ simonCell m S z ∧ simonMask m X ∈ B) *
        ((simonLiveMasks S).card : ℝ) =
      ((B.filter (· ∈ simonLiveMasks S)).card : ℝ) *
        (simonLaw m).prob (fun X => X ∈ simonCell m S z) := by
  classical
  have he := posterior_cell_expect hm hz (fun u => if u ∈ B then 1 else 0)
  have he' : (simonLaw m).prob
      (fun X => X ∈ simonCell m S z ∧ simonMask m X ∈ B) =
      (((2 ^ m - S.card).descFactorial (2 ^ m / 2 - S.card) : ℕ) : ℝ) /
        (simonPairs m).card * ((B.filter (· ∈ simonLiveMasks S)).card : ℝ) := by
    convert he using 1
    · unfold FiniteLaw.prob FiniteLaw.expect
      apply Finset.sum_congr rfl
      intro X _
      by_cases hc : X ∈ simonCell m S z <;>
        by_cases hb : simonMask m X ∈ B <;> simp [hc, hb]
    · rw [← Finset.sum_filter]
      have hcomm : (simonLiveMasks S).filter (· ∈ B) = B.filter (· ∈ simonLiveMasks S) := by
        ext u
        simp [and_comm]
      simp [hcomm]
  rw [he', posterior_cell_mass hm hz]
  ring

/-- Definition `ian:simon-law`: on a promised table, `f(x) = f(y) ↔ y = x ∨ y = x + s`. -/
theorem simonLabel_eq_iff {m : ℕ} {X : Fin (m * 2 ^ m) → Bool} (hX : X ∈ simonSupport m)
    (x y : SimonGroup m) :
    simonLabel m X x = simonLabel m X y ↔ (y = x ∨ y = x + simonMask m X) := by
  obtain ⟨s, f, hsf, rfl⟩ := hX
  rw [simonMask_simonTable hsf, simonLabel_simonTable, simonLabel_simonTable]
  exact hsf.2 x y

/-- Proof of Lemma `ian:simon-adaptive-posterior`: a collision `z x = z y` with `x ≠ y` in `S`
forces the mask `x + y` on every promised table in the cell. -/
theorem simonMask_eq_of_collision {m : ℕ} {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} {x y : SimonGroup m} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) (hzxy : z x = z y) {X : Fin (m * 2 ^ m) → Bool}
    (hXs : X ∈ simonSupport m) (hXc : X ∈ simonCell m S z) :
    simonMask m X = x + y := by
  have hf : simonLabel m X x = simonLabel m X y := (hXc x hx).trans (hzxy.trans (hXc y hy).symm)
  rcases (simonLabel_eq_iff hXs x y).mp hf with he | he
  · exact (hxy he.symm).elim
  · exact ((posterior_sum_eq x y _).mp he).symm

/-- `|E_τ| ≤ c_q = q(q-1)/2` for `q = |S|`. -/
theorem card_simonDiffs_le {m : ℕ} (S : Finset (SimonGroup m)) :
    (simonDiffs S).card ≤ S.card.choose 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [simonDiffs]
  | @insert a S ha ih =>
    have hsub : simonDiffs (insert a S) ⊆ simonDiffs S ∪ S.image (a + ·) := by
      intro u hu
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_simonDiffs _ _).mp hu
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, add_comm _ _⟩)
      · exact Finset.mem_union_left _ ((mem_simonDiffs _ _).mpr ⟨x, hx, y, hy, hxy, rfl⟩)
    calc
      _ ≤ (simonDiffs S ∪ S.image (a + ·)).card := Finset.card_le_card hsub
      _ ≤ (simonDiffs S).card + (S.image (a + ·)).card := Finset.card_union_le _ _
      _ ≤ S.card.choose 2 + S.card := Nat.add_le_add ih (Finset.card_image_le)
      _ = (insert a S).card.choose 2 := by
        rw [Finset.card_insert_of_notMem ha, Nat.choose_succ_succ]
        simp [Nat.add_comm]

/-- `|(G ∖ {0}) ∖ E_τ| + |E_τ| = M - 1` (every element of `E_τ` is nonzero). -/
theorem card_simonLiveMasks_add {m : ℕ} (S : Finset (SimonGroup m)) :
    (simonLiveMasks S).card + (simonDiffs S).card = 2 ^ m - 1 := by
  classical
  have hsub : simonDiffs S ⊆ Finset.univ.erase (0 : SimonGroup m) := by
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun he => zero_not_mem_simonDiffs S (he ▸ hu)
  have he : simonLiveMasks S = Finset.univ.erase 0 \ simonDiffs S := by
    ext u
    simp [simonLiveMasks]
  rw [he, Finset.card_sdiff_add_card_eq_card hsub]
  simp [ZMod.card]

private lemma posterior_live_card {m : ℕ} (S : Finset (SimonGroup m)) :
    ((simonLiveMasks S).card : ℝ) = (2 ^ m : ℝ) - 1 - (simonDiffs S).card := by
  have h := card_simonLiveMasks_add S
  have hp : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_pow _ _ (by omega)
  have h' : ((simonLiveMasks S).card : ℝ) + (simonDiffs S).card = (2 ^ m : ℝ) - 1 := by
    exact_mod_cast h
  linarith

/-- Centering the mask bit over all nonzero masks gives zero. -/
private lemma posterior_centered_sum {m : ℕ} (hm : 2 ≤ m) :
    ∑ u ∈ Finset.univ.erase (0 : SimonGroup m),
      ((if u ⟨0, by omega⟩ = 1 then (1 : ℝ) else 0) -
        (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1))) = 0 := by
  classical
  let F : SimonGroup m → ℝ := fun u =>
    (if u ⟨0, by omega⟩ = 1 then 1 else 0) -
      (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1))
  have hz : Set.InjOn (fun _ : SimonGroup m => (0 : SimonGroup m))
      (↑(∅ : Finset (SimonGroup m)) : Set (SimonGroup m)) := by
    simp [Set.InjOn]
  have he := posterior_cell_expect hm hz F
  have hc : simonCell m ∅ (fun _ => (0 : SimonGroup m)) = Set.univ := by
    ext X
    simp [simonCell]
  have hl : simonLiveMasks (∅ : Finset (SimonGroup m)) = Finset.univ.erase 0 := by
    ext u
    simp [simonLiveMasks, simonDiffs]
  have hmean : (simonLaw m).expect (fun X => F (simonMask m X)) = 0 := by
    simpa only [F, ← simonTarget_eq (by omega : 0 < m), simonLaw_expect_target hm] using
      (simonLaw m).expect_sub_mean (simonTarget m)
  rw [hc, Set.indicator_univ, hmean, hl] at he
  simp only [Finset.card_empty, Nat.sub_zero] at he
  have hK : (0 : ℝ) < ((2 ^ m).descFactorial (2 ^ m / 2) : ℕ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Nat.div_le_self (2 ^ m) 2)
  have hP : (0 : ℝ) < ((simonPairs m).card : ℝ) := by
    exact_mod_cast (posterior_pairs_nonempty hm).card_pos
  exact (mul_eq_zero.mp he.symm).resolve_left (div_pos hK hP).ne'

private lemma posterior_live_centered_bound {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (SimonGroup m)) :
    |∑ u ∈ simonLiveMasks S,
      ((if u ⟨0, by omega⟩ = 1 then (1 : ℝ) else 0) -
        (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)))| ≤ (simonDiffs S).card := by
  classical
  let F : SimonGroup m → ℝ := fun u =>
    (if u ⟨0, by omega⟩ = 1 then 1 else 0) -
      (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1))
  have hsub : simonDiffs S ⊆ Finset.univ.erase (0 : SimonGroup m) := by
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun he => zero_not_mem_simonDiffs S (he ▸ hu)
  have hl : simonLiveMasks S = Finset.univ.erase 0 \ simonDiffs S := by
    ext u
    simp [simonLiveMasks]
  have he : (∑ u ∈ simonLiveMasks S, F u) + ∑ u ∈ simonDiffs S, F u = 0 := by
    rw [hl, Finset.sum_sdiff hsub]
    exact posterior_centered_sum hm
  have hpow : (2 : ℝ) ≤ 2 ^ m := by
    exact_mod_cast (show 2 ≤ (2 : ℕ) ^ m from
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hr0 : 0 ≤ (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)) :=
    div_nonneg (by positivity) (by linarith)
  have hr1 : (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)) ≤ 1 := by
    apply (div_le_one (by linarith : (0 : ℝ) < 2 * (2 ^ m - 1))).mpr
    linarith
  have hb (u : SimonGroup m) : |F u| ≤ 1 := by
    dsimp [F]
    split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
  change |∑ u ∈ simonLiveMasks S, F u| ≤ _
  rw [show (∑ u ∈ simonLiveMasks S, F u) = -(∑ u ∈ simonDiffs S, F u) by linarith, abs_neg]
  calc
    _ ≤ ∑ u ∈ simonDiffs S, |F u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ simonDiffs S, (1 : ℝ) := Finset.sum_le_sum (fun u _ => hb u)
    _ = _ := by simp

/-- Lemma `ian:simon-adaptive-posterior`, unnormalised deviation bound (valid also for cells of
mass zero): `(N - e) · |E_μ[(Y - ρ_m) 1_cell]| ≤ e · μ(cell)`. -/
theorem simon_cell_deviation_le {m : ℕ} (hm : 2 ≤ m) {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S) :
    ((2 ^ m : ℝ) - 1 - (simonDiffs S).card) *
        |(simonLaw m).expect ((simonCell m S z).indicator
          (fun X => simonTarget m X - (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1))))| ≤
      ((simonDiffs S).card : ℝ) * (simonLaw m).prob (· ∈ simonCell m S z) := by
  classical
  let K : ℝ := (((2 ^ m - S.card).descFactorial (2 ^ m / 2 - S.card) : ℕ) : ℝ) /
    (simonPairs m).card
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcard := posterior_live_card S
  have he := posterior_cell_expect hm hz (fun u =>
    (if u ⟨0, by omega⟩ = 1 then (1 : ℝ) else 0) -
      (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)))
  simp only [← simonTarget_eq (by omega : 0 < m)] at he
  rw [he, abs_mul, abs_of_nonneg hK, ← hcard, posterior_cell_mass hm hz]
  change ((simonLiveMasks S).card : ℝ) * (K * |∑ u ∈ simonLiveMasks S, _|) ≤
    ((simonDiffs S).card : ℝ) * (K * (simonLiveMasks S).card)
  nlinarith [mul_le_mul_of_nonneg_left (posterior_live_centered_bound hm S)
    (mul_nonneg (show (0 : ℝ) ≤ (simonLiveMasks S).card by positivity) hK)]

private lemma posterior_cond_centered {A : Type*} [Fintype A] (μ : FiniteLaw A)
    (H : Set A) (hpos : 0 < μ.prob (· ∈ H)) (f : A → ℝ) (r : ℝ) :
    (condLaw μ H hpos).expect f - r =
      μ.expect (H.indicator (fun X => f X - r)) / μ.prob (· ∈ H) := by
  classical
  have he : (condLaw μ H hpos).expect f = μ.expect (H.indicator f) / μ.prob (· ∈ H) := by
    unfold FiniteLaw.expect condLaw
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ H
    · simp only [hx, if_true, Set.indicator_of_mem]
      ring
    · simp [hx]
  have hc : μ.expect (H.indicator (fun X => f X - r)) =
      μ.expect (H.indicator f) - r * μ.prob (· ∈ H) := by
    unfold FiniteLaw.expect FiniteLaw.prob
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ H
    · simp only [Set.indicator_of_mem hx, if_pos hx]
      ring
    · simp [hx]
  rw [he, hc]
  field_simp

/-- Lemma `ian:simon-adaptive-posterior`, deviation bound: on a collision-free transcript of
positive probability, with `e = |E_τ|` and `N = M - 1`,
`|E[Y | τ] - ρ_m| ≤ e / (N - e)` (and `e < N`). -/
theorem simon_posterior_target_bound {m : ℕ} (hm : 2 ≤ m) {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S)
    (hpos : 0 < (simonLaw m).prob (· ∈ simonCell m S z)) :
    ((simonDiffs S).card : ℝ) < (2 ^ m : ℝ) - 1 ∧
      |(condLaw (simonLaw m) (simonCell m S z) hpos).expect (simonTarget m) -
          (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1))| ≤
        ((simonDiffs S).card : ℝ) / ((2 ^ m : ℝ) - 1 - (simonDiffs S).card) := by
  classical
  have hcard := posterior_live_card S
  have hl : 0 < (simonLiveMasks S).card := by
    by_contra hn
    have he : (simonLiveMasks S).card = 0 := by omega
    rw [posterior_cell_mass hm hz, he, Nat.cast_zero, mul_zero] at hpos
    exact (lt_irrefl 0 hpos)
  have hn : (0 : ℝ) < (2 ^ m : ℝ) - 1 - (simonDiffs S).card := by
    rw [← hcard]
    exact_mod_cast hl
  refine ⟨by linarith, ?_⟩
  rw [posterior_cond_centered, abs_div, abs_of_pos hpos]
  apply (div_le_div_iff₀ hpos hn).mpr
  simpa [mul_comm] using simon_cell_deviation_le hm hz

/-- Proof of Lemma `ian:simon-adaptive-posterior`, one collision step: on a collision-free cell,
the next argument `x` collides iff the mask lies in `B = {x + x_i : x_i ∈ S}`, and
`μ(cell, s ∈ B) · (N - e) ≤ |S| · μ(cell)`. -/
theorem simon_collision_step_le {m : ℕ} (hm : 2 ≤ m) {S : Finset (SimonGroup m)}
    {z : SimonGroup m → SimonGroup m} (hz : Set.InjOn z S) (x : SimonGroup m) :
    (simonLaw m).prob (fun X => X ∈ simonCell m S z ∧ simonMask m X ∈ S.image (x + ·)) *
        ((2 ^ m : ℝ) - 1 - (simonDiffs S).card) ≤
      (S.card : ℝ) * (simonLaw m).prob (· ∈ simonCell m S z) := by
  classical
  have hcard := posterior_live_card S
  rw [← hcard, simon_posterior_uniform hm hz]
  apply mul_le_mul_of_nonneg_right _ ((simonLaw m).prob_nonneg _)
  exact_mod_cast (le_trans (Finset.card_filter_le _ _) (Finset.card_image_le))

end UnifiedAA.HardSector
