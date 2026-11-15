import UnifiedAA.HardSector.Basic
import UnifiedAA.Uniform
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The randomly labelled Simon law (HS3.1)

Source: `notes/ian/30_simon_sector.tex`, Definition `ian:simon-law` and Lemma
`ian:simon-promise-count`.

Encoding, fixed here and reused by all Simon modules:
* `G = SimonGroup m = Fin m → ZMod 2` is `𝔽₂^m`, `M = 2^m`.
* Table coordinates are `Fin (m * 2^m)`, identified with pairs `(j, x) : Fin m × G` by
  `simonCoord m` (`finProdFinEquiv` then `finFunctionFinEquiv`); the bijection is a fixed
  relabelling.
* The table of `f : G → G` is `X (j,x) = true ↔ f(x)_j = 1` (the TeX's `X_{x,j} = (-1)^{f(x)_j}`,
  with `-1 ↦ true`).
* `simonLaw m` is the push-forward, to tables, of the uniform law on admissible pairs `(s, f)`:
  `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`. Every mask has the same number of admissible
  labellings (`(M)_{M/2}` injections of the `M/2` pairs), so this is the TeX's "s uniform, then
  `L` uniform".
* `Y = simonTarget m` is the first bit of the mask of a promised table, and `0` off the promise.
-/

namespace UnifiedAA.HardSector

open scoped BigOperators

-- LOCK BEGIN
/-- Push-forward of the uniform law on a nonempty finset `S` along `g`. -/
noncomputable def uniformPushforward {A B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset A) (hS : S.Nonempty) (g : A → B) : FiniteLaw B where
  weight b := ((S.filter (fun a => g a = b)).card : ℝ) / S.card
  nonneg b := by positivity
  total := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have h : (∑ b, ((S.filter (fun a => g a = b)).card : ℝ)) = S.card := by
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise
        (f := g) (s := S) (t := Finset.univ) (fun a _ => Finset.mem_coe.2 (Finset.mem_univ _))).symm
    rw [h]
    exact mul_inv_cancel₀ (by exact_mod_cast hS.card_pos.ne')

/-- The point mass at `b`. -/
noncomputable def diracLaw {B : Type*} [Fintype B] [DecidableEq B] (b : B) : FiniteLaw B where
  weight x := if x = b then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  total := by simp

/-- `G = 𝔽₂^m`. -/
abbrev SimonGroup (m : ℕ) := Fin m → ZMod 2

/-- Table coordinates `Fin (m * 2^m) ≃ Fin m × G`: coordinate `(j, x)` is bit `j` of `f(x)`. -/
def simonCoord (m : ℕ) : Fin (m * 2 ^ m) ≃ Fin m × SimonGroup m :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv.symm)

/-- Admissible pairs (Definition `ian:simon-law`): `s ≠ 0` and `f(x) = f(y) ↔ y ∈ {x, x + s}`. -/
def IsSimonPair {m : ℕ} (s : SimonGroup m) (f : SimonGroup m → SimonGroup m) : Prop :=
  s ≠ 0 ∧ ∀ x y, f x = f y ↔ (y = x ∨ y = x + s)

/-- The finset of admissible pairs. -/
noncomputable def simonPairs (m : ℕ) :
    Finset (SimonGroup m × (SimonGroup m → SimonGroup m)) := by
  classical
  exact Finset.univ.filter (fun p => IsSimonPair p.1 p.2)

/-- The table of `f`: coordinate `(j, x)` is `true` iff `f(x)_j = 1`. -/
def simonTable {m : ℕ} (f : SimonGroup m → SimonGroup m) : Fin (m * 2 ^ m) → Bool :=
  fun i => decide (f (simonCoord m i).2 (simonCoord m i).1 = 1)

/-- The randomly labelled Simon law `μ^{(m)}` on `Ω_{n_m}`, `n_m = m 2^m`. (For `m = 0` there
is no admissible pair; a point mass is used so that the definition is total.) -/
noncomputable def simonLaw (m : ℕ) : FiniteLaw (Fin (m * 2 ^ m) → Bool) := by
  classical
  exact if h : (simonPairs m).Nonempty then
      uniformPushforward (simonPairs m) h (fun p => simonTable p.2)
    else diracLaw (fun _ => false)

/-- `H_m`: the promised tables (Lemma `ian:simon-promise-count` shows this is the support). -/
def simonSupport (m : ℕ) : Set (Fin (m * 2 ^ m) → Bool) :=
  {X | ∃ s f, IsSimonPair s f ∧ simonTable f = X}

/-- The mask of a promised table (`0` off the promise). -/
noncomputable def simonMask (m : ℕ) (X : Fin (m * 2 ^ m) → Bool) : SimonGroup m := by
  classical
  exact if h : ∃ s f, IsSimonPair s f ∧ simonTable f = X then Classical.choose h else 0

/-- The target `Y = s_1` (Definition `ian:simon-law`), as a real in `{0,1}`; `0` if `m = 0`. -/
noncomputable def simonTarget (m : ℕ) (X : Fin (m * 2 ^ m) → Bool) : ℝ := by
  classical
  exact if hm : 0 < m then (if simonMask m X ⟨0, hm⟩ = 1 then 1 else 0) else 0
-- LOCK END

open scoped Classical

/-- A coordinate of a binary vector is either zero or one. -/
private lemma bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Lemma `ian:simon-promise-count`: a table determines its labelling and its mask. -/
theorem isSimonPair_unique {m : ℕ} {s s' : SimonGroup m} {f f' : SimonGroup m → SimonGroup m}
    (h : IsSimonPair s f) (h' : IsSimonPair s' f') (hX : simonTable f = simonTable f') :
    s = s' ∧ f = f' := by
  have hf : f = f' := by
    funext x j
    have hb := congrFun hX ((simonCoord m).symm (j, x))
    simp only [simonTable, Equiv.apply_symm_apply] at hb
    have he : (f x j = 1) ↔ (f' x j = 1) := decide_eq_decide.mp hb
    rcases bit_cases (f x j) with ha | ha <;>
      rcases bit_cases (f' x j) with hb | hb <;> simp_all
  refine ⟨?_, hf⟩
  have hs : f 0 = f s := (h.2 0 s).2 (Or.inr (by simp))
  rw [hf] at hs
  rcases (h'.2 0 s).1 hs with hz | hz
  · exact (h.1 hz).elim
  · simpa using hz

/-- The mask read off a promised table is its mask. -/
theorem simonMask_simonTable {m : ℕ} {s : SimonGroup m} {f : SimonGroup m → SimonGroup m}
    (h : IsSimonPair s f) : simonMask m (simonTable f) = s := by
  classical
  have hex : ∃ t g, IsSimonPair t g ∧ simonTable g = simonTable f := ⟨s, f, h, rfl⟩
  rw [simonMask, dif_pos hex]
  obtain ⟨g, hg, hX⟩ := Classical.choose_spec hex
  exact (isSimonPair_unique hg h hX).1

private lemma simon_twice {m : ℕ} (x u : SimonGroup m) : x + u + u = x := by
  funext j
  change x j + u j + u j = x j
  rw [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

/-- Representatives for the pairs are the vectors with a chosen bit zero. -/
private abbrev PairRep (m : ℕ) (i : Fin m) := {x : SimonGroup m // x i = 0}

private def pairRep {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x : SimonGroup m) : PairRep m i :=
  ⟨if x i = 0 then x else x + u, by
    split_ifs with h
    · exact h
    · have hx := (bit_cases (x i)).resolve_left h
      simp [hx, hi]; decide⟩

private lemma pairRep_of_zero {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x : PairRep m i) : pairRep u i hi x = x := by
  apply Subtype.ext
  simp [pairRep, x.property]

private lemma pairRep_add {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x : SimonGroup m) : pairRep u i hi (x + u) = pairRep u i hi x := by
  apply Subtype.ext
  have htwo : (1 + 1 : ZMod 2) = 0 := rfl
  rcases bit_cases (x i) with hx | hx <;>
    simp [pairRep, Pi.add_apply, hx, hi, simon_twice, htwo]

private lemma pairRep_eq_iff {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1)
    (x y : SimonGroup m) :
    pairRep u i hi x = pairRep u i hi y ↔ y = x ∨ y = x + u := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    dsimp [pairRep] at h'
    split_ifs at h' with hx hy hy
    · exact Or.inl h'.symm
    · exact Or.inr (by rw [h', simon_twice])
    · exact Or.inr h'.symm
    · exact Or.inl (add_right_cancel h').symm
  · rintro (rfl | rfl)
    · rfl
    · exact (pairRep_add u i hi x).symm

private def pairSplit {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1) :
    SimonGroup m ≃ PairRep m i × Bool where
  toFun x := (pairRep u i hi x, decide (x i ≠ 0))
  invFun p := if p.2 then p.1.val + u else p.1.val
  left_inv x := by
    by_cases hx : x i = 0 <;> simp [pairRep, hx, simon_twice]
  right_inv p := by
    rcases p with ⟨x, b⟩
    cases b
    · simp [pairRep_of_zero, x.property]
    · simp [pairRep_add, pairRep_of_zero, Pi.add_apply, x.property, hi]

private lemma card_pairRep {m : ℕ} (u : SimonGroup m) (i : Fin m) (hi : u i = 1) :
    Fintype.card (PairRep m i) = 2 ^ m / 2 := by
  have hc := Fintype.card_congr (pairSplit u i hi)
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool] at hc
  omega

/-- Restriction to the representatives identifies admissible functions with injections. -/
private def labelEquiv {m : ℕ} (u : SimonGroup m) (hu : u ≠ 0)
    (i : Fin m) (hi : u i = 1) :
    {f : SimonGroup m → SimonGroup m // IsSimonPair u f} ≃ (PairRep m i ↪ SimonGroup m) where
  toFun f := ⟨fun x => f.val x.val, by
    intro x y h
    apply Subtype.ext
    rcases (f.property.2 x y).1 h with hxy | hxy
    · exact hxy.symm
    · have he := congrFun hxy i
      simp [Pi.add_apply, x.property, y.property, hi] at he⟩
  invFun e := ⟨fun x => e (pairRep u i hi x), hu, by
    intro x y
    rw [e.injective.eq_iff, pairRep_eq_iff]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    apply (f.property.2 _ _).2
    dsimp [pairRep]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (by rw [simon_twice])
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    exact congrArg e (pairRep_of_zero u i hi x)

private lemma card_labels {m : ℕ} {u : SimonGroup m} (hu : u ≠ 0) :
    Fintype.card {f : SimonGroup m → SimonGroup m // IsSimonPair u f} =
      (2 ^ m).descFactorial (2 ^ m / 2) := by
  classical
  have hex : ∃ i, u i ≠ 0 := by
    by_contra h
    apply hu
    ext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hex
  have hi' := (bit_cases (u i)).resolve_left hi
  rw [Fintype.card_congr (labelEquiv u hu i hi'), Fintype.card_embedding_eq,
    card_pairRep u i hi']
  simp [ZMod.card]

private lemma card_fiber {m : ℕ} {u : SimonGroup m} (hu : u ≠ 0) :
    ((simonPairs m).filter (fun p => p.1 = u)).card =
      (2 ^ m).descFactorial (2 ^ m / 2) := by
  classical
  rw [← card_labels hu, Fintype.card_subtype]
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    simp only [Finset.mem_filter, simonPairs, Finset.mem_univ, true_and] at hp ⊢
    exact hp.2 ▸ hp.1
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hp'.trans hq'.symm) he
  · intro f hf
    refine ⟨(u, f), ?_, rfl⟩
    simpa [simonPairs] using hf

/-- Count pairs whose masks lie in a prescribed finite set of nonzero vectors. -/
private lemma card_pairs_masks {m : ℕ} (T : Finset (SimonGroup m)) (hT : ∀ u ∈ T, u ≠ 0) :
    ((simonPairs m).filter (fun p => p.1 ∈ T)).card =
      T.card * (2 ^ m).descFactorial (2 ^ m / 2) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := (simonPairs m).filter (fun p => p.1 ∈ T)) (f := Prod.fst) (t := T)
    (fun p hp => (Finset.mem_filter.mp hp).2)]
  apply Finset.sum_const_nat
  intro u hu
  have he : (((simonPairs m).filter (fun p => p.1 ∈ T)).filter (fun p => p.1 = u)) =
      (simonPairs m).filter (fun p => p.1 = u) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hp, he⟩
      exact ⟨⟨hp, he ▸ hu⟩, he⟩
  rw [he]
  exact card_fiber (hT u hu)

private lemma card_pairs (m : ℕ) :
    (simonPairs m).card = (2 ^ m - 1) * (2 ^ m).descFactorial (2 ^ m / 2) := by
  classical
  have he : (simonPairs m).filter (fun p => p.1 ∈ Finset.univ.erase 0) = simonPairs m := by
    apply Finset.filter_true_of_mem
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    simpa using h.1
  have hc := card_pairs_masks (Finset.univ.erase (0 : SimonGroup m))
    (by simp)
  rw [he] at hc
  simpa [Fintype.card_fun, ZMod.card] using hc

private lemma pairs_nonempty {m : ℕ} (hm : 2 ≤ m) : (simonPairs m).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_pairs]
  apply Nat.mul_pos
  · have : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by omega)
    omega
  · exact Nat.descFactorial_pos.mpr (Nat.div_le_self _ _)

private lemma table_injective {m : ℕ} :
    Set.InjOn (fun p : SimonGroup m × (SimonGroup m → SimonGroup m) => simonTable p.2)
      (simonPairs m) := by
  intro p hp q hq he
  have h := isSimonPair_unique (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
  exact Prod.ext h.1 h.2

private lemma support_image (m : ℕ) :
    simonSupport m = ↑((simonPairs m).image (fun p => simonTable p.2)) := by
  classical
  ext X
  simp [simonSupport, simonPairs]

/-- Lemma `ian:simon-promise-count`: `|H_m| = (M - 1)(M)_{M/2}`. -/
theorem card_simonSupport {m : ℕ} (hm : 2 ≤ m) :
    (simonSupport m).ncard = (2 ^ m - 1) * (2 ^ m).descFactorial (2 ^ m / 2) := by
  classical
  rw [support_image, Set.ncard_coe_finset, Finset.card_image_iff.mpr table_injective,
    card_pairs]

/-- Lemma `ian:simon-promise-count`: `μ^{(m)}` is uniform on `H_m`. -/
theorem simonLaw_weight_of_mem {m : ℕ} (hm : 2 ≤ m) {X : Fin (m * 2 ^ m) → Bool}
    (hX : X ∈ simonSupport m) :
    (simonLaw m).weight X = 1 / (((2 ^ m - 1) * (2 ^ m).descFactorial (2 ^ m / 2) : ℕ) : ℝ) := by
  classical
  obtain ⟨s, f, hsf, rfl⟩ := hX
  have hmem : (s, f) ∈ simonPairs m := by simpa [simonPairs] using hsf
  have he : (simonPairs m).filter (fun p => simonTable p.2 = simonTable f) = {(s, f)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, he⟩
      exact table_injective hp hmem he
    · rintro rfl
      exact ⟨hmem, rfl⟩
  simp [simonLaw, pairs_nonempty hm, uniformPushforward, he, card_pairs]

/-- Lemma `ian:simon-promise-count`: `μ^{(m)}` vanishes off `H_m` (so `H_m = supp μ^{(m)}`). -/
theorem simonLaw_weight_of_not_mem {m : ℕ} (hm : 2 ≤ m) {X : Fin (m * 2 ^ m) → Bool}
    (hX : X ∉ simonSupport m) : (simonLaw m).weight X = 0 := by
  classical
  have he : (simonPairs m).filter (fun p => simonTable p.2 = X) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp he
    exact hX ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, he⟩
  simp [simonLaw, pairs_nonempty hm, uniformPushforward, he]

/-- `μ^{(m)}(H_m) = 1` (used as "weight one" in Theorem `ian:simon-sector-theorem`). -/
theorem simonLaw_prob_support {m : ℕ} (hm : 2 ≤ m) :
    (simonLaw m).prob (· ∈ simonSupport m) = 1 := by
  classical
  rw [FiniteLaw.prob, ← (simonLaw m).total]
  apply Finset.sum_congr rfl
  intro X _
  by_cases hX : X ∈ simonSupport m
  · simp [hX]
  · simp [hX, simonLaw_weight_of_not_mem hm hX]

/-- Proof of Lemma `ian:simon-promise-count`: each nonzero mask has exactly `(M)_{M/2}`
admissible labellings. -/
theorem card_simonPair_fiber {m : ℕ} (hm : 2 ≤ m) {u : SimonGroup m} (hu : u ≠ 0) :
    ((simonPairs m).filter (fun p => p.1 = u)).card = (2 ^ m).descFactorial (2 ^ m / 2) := by
  exact card_fiber hu

/-- Unfolding `simonTarget` for `m > 0`. -/
theorem simonTarget_eq {m : ℕ} (hm : 0 < m) (X : Fin (m * 2 ^ m) → Bool) :
    simonTarget m X = if simonMask m X ⟨0, hm⟩ = 1 then 1 else 0 := by
  simp [simonTarget, hm]

private lemma expect_pushforward {A B : Type*} [Fintype B] [DecidableEq B]
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

private lemma card_bit_one {m : ℕ} (i : Fin m) :
    (Finset.univ.filter (fun x : SimonGroup m => x i = 1)).card = 2 ^ m / 2 := by
  classical
  let v : SimonGroup m := Function.update 0 i 1
  have hv : v i = 1 := by simp [v]
  have htwo : (1 + 1 : ZMod 2) = 0 := rfl
  have he : (Finset.univ.filter (fun x : SimonGroup m => x i = 1)).card =
      (Finset.univ.filter (fun x : SimonGroup m => x i = 0)).card := by
    apply Finset.card_bij (fun x _ => x + v)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simp [Pi.add_apply, hx, hv, htwo]
    · intro x _ y _ he
      exact add_right_cancel he
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨y + v, ?_, simon_twice y v⟩
      simp [Pi.add_apply, hy, hv]
  rw [he, ← Fintype.card_subtype]
  exact card_pairRep v i hv

private lemma real_pow_gt_one {m : ℕ} (hm : 2 ≤ m) : (1 : ℝ) < 2 ^ m := by
  exact one_lt_pow₀ (by norm_num) (by omega)

/-- Lemma `ian:simon-promise-count`: `ρ_m = E Y = M / (2(M - 1))`. -/
theorem simonLaw_expect_target {m : ℕ} (hm : 2 ≤ m) :
    (simonLaw m).expect (simonTarget m) = (2 ^ m : ℝ) / (2 * ((2 ^ m : ℝ) - 1)) := by
  classical
  have hm0 : 0 < m := by omega
  let i : Fin m := ⟨0, hm0⟩
  let T := Finset.univ.filter (fun u : SimonGroup m => u i = 1)
  have hT : ∀ u ∈ T, u ≠ 0 := by
    intro u hu hz
    have he : u i = 1 := (Finset.mem_filter.mp hu).2
    rw [hz] at he
    exact zero_ne_one he
  have hc := card_pairs_masks T hT
  have hnum : (∑ p ∈ simonPairs m, simonTarget m (simonTable p.2)) =
      (((2 ^ m / 2) * (2 ^ m).descFactorial (2 ^ m / 2) : ℕ) : ℝ) := by
    calc
      _ = ∑ p ∈ simonPairs m, if p.1 ∈ T then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [simonTarget_eq hm0, simonMask_simonTable (Finset.mem_filter.mp hp).2]
        simp [T, i]
      _ = (((simonPairs m).filter (fun p => p.1 ∈ T)).card : ℝ) := by
        simp
      _ = _ := by rw [hc, card_bit_one]
  rw [simonLaw, dif_pos (pairs_nonempty hm), expect_pushforward, hnum, card_pairs]
  have hD : (0 : ℝ) < ((2 ^ m).descFactorial (2 ^ m / 2) : ℕ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (Nat.div_le_self (2 ^ m) 2))
  have hpow : 1 < (2 : ℝ) ^ m := real_pow_gt_one hm
  have heven : 2 ^ m / 2 * 2 = 2 ^ m := by
    have hd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    exact Nat.div_mul_cancel hd
  have hhalf : ((2 ^ m / 2 : ℕ) : ℝ) * 2 = (2 : ℝ) ^ m := by exact_mod_cast heven
  push_cast [Nat.cast_sub (by have := Nat.one_le_pow m 2 (by omega); omega)]
  field_simp [ne_of_gt hD, ne_of_gt (sub_pos.mpr hpow)]
  nlinarith

/-- Lemma `ian:simon-promise-count`:
`Var Y = M(M - 2)/(4(M - 1)^2) = 1/4 - 1/(4(M - 1)^2)`. -/
theorem simonLaw_variance_target {m : ℕ} (hm : 2 ≤ m) :
    (simonLaw m).variance (simonTarget m) =
        (2 ^ m : ℝ) * ((2 ^ m : ℝ) - 2) / (4 * ((2 ^ m : ℝ) - 1) ^ 2) ∧
      (simonLaw m).variance (simonTarget m) = 1 / 4 - 1 / (4 * ((2 ^ m : ℝ) - 1) ^ 2) := by
  classical
  let μ := simonLaw m
  let Y := simonTarget m
  have hsq : (fun X => Y X ^ 2) = Y := by
    funext X
    simp only [Y, simonTarget]
    split_ifs <;> norm_num
  have hv : μ.variance Y = μ.expect Y - (μ.expect Y) ^ 2 := by
    have he := μ.mse_eq_variance_add_sq Y 0
    simp only [sub_zero, hsq] at he
    linarith
  change μ.variance Y = _ ∧ μ.variance Y = _
  rw [hv]
  change (simonLaw m).expect (simonTarget m) -
    ((simonLaw m).expect (simonTarget m)) ^ 2 = _ ∧ _
  rw [simonLaw_expect_target hm]
  have hp := real_pow_gt_one hm
  constructor <;> field_simp [ne_of_gt (sub_pos.mpr hp)] <;> ring

/-- Lemma `ian:simon-promise-count`: `U_{n_m}(H_m) = (M - 1)(M)_{M/2}/M^M ≤ (M - 1) M^{-M/2}`. -/
theorem uniform_prob_simonSupport {m : ℕ} (hm : 2 ≤ m) :
    (FiniteLaw.uniform (Fin (m * 2 ^ m) → Bool)).prob (· ∈ simonSupport m) =
        (((2 ^ m - 1) * (2 ^ m).descFactorial (2 ^ m / 2) : ℕ) : ℝ) / (2 ^ m : ℝ) ^ (2 ^ m) ∧
      (FiniteLaw.uniform (Fin (m * 2 ^ m) → Bool)).prob (· ∈ simonSupport m) ≤
        ((2 ^ m : ℝ) - 1) / (2 ^ m : ℝ) ^ (2 ^ m / 2) := by
  classical
  have hcard : Fintype.card (Fin (m * 2 ^ m) → Bool) = (2 ^ m) ^ (2 ^ m) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← Nat.pow_mul]
  have hc : (Finset.univ.filter (fun X => X ∈ simonSupport m)).card =
      (simonSupport m).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext X
    simp
  have he : (FiniteLaw.uniform (Fin (m * 2 ^ m) → Bool)).prob (· ∈ simonSupport m) =
      (((2 ^ m - 1) * (2 ^ m).descFactorial (2 ^ m / 2) : ℕ) : ℝ) /
        (2 ^ m : ℝ) ^ (2 ^ m) := by
    unfold FiniteLaw.prob FiniteLaw.uniform
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hc, card_simonSupport hm, hcard,
      Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul]
  refine ⟨he, ?_⟩
  rw [he]
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hM1 : (1 : ℝ) ≤ 2 ^ m := (real_pow_gt_one hm).le
  have hbound : (((2 ^ m).descFactorial (2 ^ m / 2) : ℕ) : ℝ) ≤
      (2 ^ m : ℝ) ^ (2 ^ m / 2) := by
    exact_mod_cast Nat.descFactorial_le_pow (2 ^ m) (2 ^ m / 2)
  have heven : 2 ^ m / 2 + 2 ^ m / 2 = 2 ^ m := by
    have hd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have := Nat.div_mul_cancel hd
    omega
  have hsplit : (2 ^ m : ℝ) ^ (2 ^ m) =
      (2 ^ m : ℝ) ^ (2 ^ m / 2) * (2 ^ m : ℝ) ^ (2 ^ m / 2) := by
    rw [← pow_add, heven]
  have hnat : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_pow m 2 (by omega)
  push_cast [Nat.cast_sub hnat]
  rw [hsplit]
  calc
    ((2 ^ m : ℝ) - 1) * ((2 ^ m).descFactorial (2 ^ m / 2) : ℕ) /
        ((2 ^ m : ℝ) ^ (2 ^ m / 2) * (2 ^ m : ℝ) ^ (2 ^ m / 2)) ≤
        ((2 ^ m : ℝ) - 1) * (2 ^ m : ℝ) ^ (2 ^ m / 2) /
        ((2 ^ m : ℝ) ^ (2 ^ m / 2) * (2 ^ m : ℝ) ^ (2 ^ m / 2)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hM1)) (by positivity)
    _ = _ := by field_simp

end UnifiedAA.HardSector
