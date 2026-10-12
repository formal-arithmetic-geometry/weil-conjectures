/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.Derived

/-!
# Iterated derived couples

Let `X = (D, E, α, f, g)` be an exact couple (of type `0`). Its iterated derived couples
`X.iter k` (`k : ℕ`), with `X.iter 0 = X` and `X.iter (k + 1) = (X.iter k).derived`, are exact
couples of type `k`. In the indexing of the blueprint the couple `X.iter k` is `C_{k+2}`, so that
`(X.iter k).E` is the page `E_{k+2}` of the spectral sequence of the couple, with differential
`d_{k+2}` of bidegree `(k + 2, -k - 1)`.

The `D`-terms of `X.iter k` are subobjects of those of `X` (`CategoryTheory.ExactCouple.ιIter`),
and `D_{k+2}^{p,q}` is the image of `α^k : D^{p+k,q-k} ⟶ D^{p,q}`
(`CategoryTheory.ExactCouple.imageSubobject_αPow`); this is claim 4 of
`lem-sp-derived-couple-exact`.

## Main definitions

- `CategoryTheory.ExactCouple.αPow`: the iterates `α^k : D^{a,b} ⟶ D^{a-k,b+k}`.
- `CategoryTheory.ExactCouple.iter`: the iterated derived couples.
- `CategoryTheory.ExactCouple.ιIter`: the inclusion `D_{k+2}^{p,q} ⟶ D^{p,q}`.
- `CategoryTheory.ExactCouple.αbarIter`: the corestriction `D^{p+k,q-k} ⟶ D_{k+2}^{p,q}` of
  `α^k`, an epimorphism.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ExactCouple

variable {C : Type*} [Category* C] [Abelian C]

section αPow

variable {s : ℕ} (X : ExactCouple C s)

/-- The iterate `α^k : D^{a,b} ⟶ D^{p,q}` with `(p, q) = (a - k, b + k)`. -/
noncomputable def αPow : (k : ℕ) → (a b p q : ℤ) → (ha : p + k = a) → (hb : b + k = q) →
    X.D a b ⟶ X.D p q
  | 0, a, b, p, q, ha, hb => eqToHom (by
      obtain rfl : a = p := by lia
      obtain rfl : b = q := by lia
      rfl)
  | k + 1, a, b, p, q, ha, hb =>
      X.α a b (a - 1) (b + 1) ≫ αPow k (a - 1) (b + 1) p q (by lia) (by lia)

@[simp]
lemma αPow_zero (a b : ℤ) : X.αPow 0 a b a b (by simp) (by simp) = 𝟙 _ := rfl

lemma αPow_zero' (a b p q : ℤ) (ha : p + (0 : ℕ) = a) (hb : b + (0 : ℕ) = q) :
    X.αPow 0 a b p q ha hb = eqToHom (by
      obtain rfl : a = p := by lia
      obtain rfl : b = q := by lia
      rfl) := rfl

lemma αPow_succ (k : ℕ) (a b p q : ℤ) (ha : p + (k + 1 : ℕ) = a) (hb : b + (k + 1 : ℕ) = q) :
    X.αPow (k + 1) a b p q ha hb =
      X.α a b (a - 1) (b + 1) ≫ X.αPow k (a - 1) (b + 1) p q (by lia) (by lia) := rfl

lemma αPow_one (a b p q : ℤ) (ha : p + (1 : ℕ) = a) (hb : b + (1 : ℕ) = q) :
    X.αPow 1 a b p q ha hb = X.α a b p q (by lia) (by lia) := by
  obtain rfl : p = a - 1 := by lia
  obtain rfl : q = b + 1 := by lia
  simp [αPow_succ]

lemma αPow_congr (k k' : ℕ) (h : k = k') {a b p q : ℤ} (ha : p + k = a) (hb : b + k = q) :
    X.αPow k a b p q ha hb = X.αPow k' a b p q (by subst h; exact ha) (by subst h; exact hb) := by
  subst h
  rfl

lemma αPow_add (m n : ℕ) (a b c d p q : ℤ) (hc : c + m = a) (hd : b + m = d)
    (hp : p + n = c) (hq : d + n = q) (ha : p + (m + n : ℕ) = a) (hb : b + (m + n : ℕ) = q) :
    X.αPow (m + n) a b p q ha hb =
      X.αPow m a b c d hc hd ≫ X.αPow n c d p q hp hq := by
  induction m generalizing a b with
  | zero =>
    obtain rfl : c = a := by lia
    obtain rfl : d = b := by lia
    simp
  | succ m ih =>
    rw [X.αPow_congr (m + 1 + n) (m + n + 1) (by lia), αPow_succ, αPow_succ, assoc,
      ih (a - 1) (b + 1) (by lia) (by lia)]

lemma αPow_succ' (k : ℕ) (a b p q : ℤ) (ha : p + (k + 1 : ℕ) = a) (hb : b + (k + 1 : ℕ) = q) :
    X.αPow (k + 1) a b p q ha hb =
      X.αPow k a b (p + 1) (q - 1) (by lia) (by lia) ≫ X.α (p + 1) (q - 1) p q := by
  rw [X.αPow_add k 1 a b (p + 1) (q - 1) p q (by lia) (by lia) (by lia) (by lia), αPow_one]

end αPow

variable (X : ExactCouple C 0)

/-- The iterated derived couples: `X.iter 0 = X` and `X.iter (k + 1) = (X.iter k).derived`, an
exact couple of type `k`. In the blueprint numbering `X.iter k` is the couple `C_{k+2}`, whose
`E`-terms are the page `E_{k+2}` of the spectral sequence of `X`
(`lem-sp-derived-couple-exact`, claim 4). -/
noncomputable def iter : (k : ℕ) → ExactCouple C k
  | 0 => X
  | k + 1 => (iter k).derived

@[simp]
lemma iter_zero : X.iter 0 = X := rfl

lemma iter_succ (k : ℕ) : X.iter (k + 1) = (X.iter k).derived := rfl

/-- The inclusion `D_{k+2}^{p,q} ⟶ D^{p,q}` of the `D`-terms of the iterated couples. -/
noncomputable def ιIter : (k : ℕ) → (p q : ℤ) → (X.iter k).D p q ⟶ X.D p q
  | 0, _, _ => 𝟙 _
  | k + 1, p, q => (X.iter k).ι' p q ≫ ιIter k p q

@[simp]
lemma ιIter_zero (p q : ℤ) : X.ιIter 0 p q = 𝟙 _ := rfl

lemma ιIter_succ (k : ℕ) (p q : ℤ) :
    X.ιIter (k + 1) p q = (X.iter k).ι' p q ≫ X.ιIter k p q := rfl

instance (k : ℕ) (p q : ℤ) : Mono (X.ιIter k p q) := by
  induction k with
  | zero => exact (inferInstance : Mono (𝟙 _))
  | succ k ih => rw [ιIter_succ]; infer_instance

/-- The map `α` of the iterated couple is the restriction of `α`. -/
@[reassoc]
lemma iter_α_ιIter (k : ℕ) (p q p' q' : ℤ) (hp : p' + 1 = p) (hq : q + 1 = q') :
    (X.iter k).α p q p' q' ≫ X.ιIter k p' q' = X.ιIter k p q ≫ X.α p q p' q' := by
  induction k with
  | zero => simp [ιIter, iter]
  | succ k ih =>
    change (X.iter k).α' p q p' q' ≫ (X.iter k).ι' p' q' ≫ X.ιIter k p' q' =
      ((X.iter k).ι' p q ≫ X.ιIter k p q) ≫ X.α p q p' q'
    rw [← assoc, (X.iter k).α'_ι' p q p' q', assoc, ih, assoc]

/-- The corestriction `D^{a,b} ⟶ D_{k+2}^{p,q}` of `α^k : D^{a,b} ⟶ D^{p,q}`
(`(p, q) = (a - k, b + k)`), an epimorphism. -/
noncomputable def αbarIter : (k : ℕ) → (a b p q : ℤ) → (ha : p + k = a) → (hb : b + k = q) →
    X.D a b ⟶ (X.iter k).D p q
  | 0, a, b, p, q, ha, hb => X.αPow 0 a b p q ha hb
  | k + 1, a, b, p, q, ha, hb =>
      αbarIter k a b (p + 1) (q - 1) (by lia) (by lia) ≫
        (X.iter k).αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1)

lemma αbarIter_succ (k : ℕ) (a b p q : ℤ) (ha : p + (k + 1 : ℕ) = a)
    (hb : b + (k + 1 : ℕ) = q) :
    X.αbarIter (k + 1) a b p q ha hb = X.αbarIter k a b (p + 1) (q - 1) (by lia) (by lia) ≫
        (X.iter k).αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1) := rfl

instance (k : ℕ) (a b p q : ℤ) (ha : p + k = a) (hb : b + k = q) :
    Epi (X.αbarIter k a b p q ha hb) := by
  induction k generalizing p q with
  | zero => exact (inferInstance : Epi (eqToHom _))
  | succ k ih =>
    rw [αbarIter_succ]
    have := ih (p + 1) (q - 1) (by lia) (by lia)
    exact epi_comp' this ((X.iter k).epi_αbar _ _ _ _ _ _)

@[reassoc (attr := simp)]
lemma αbarIter_ιIter (k : ℕ) (a b p q : ℤ) (ha : p + k = a) (hb : b + k = q) :
    X.αbarIter k a b p q ha hb ≫ X.ιIter k p q = X.αPow k a b p q ha hb := by
  induction k generalizing p q with
  | zero => simp [αbarIter, ιIter]
  | succ k ih =>
    rw [αbarIter_succ, ιIter_succ, assoc, (X.iter k).αbar_ι'_assoc (p + 1) (q - 1) p q,
      X.iter_α_ιIter k (p + 1) (q - 1) p q rfl (sub_add_cancel q 1), ← assoc, ih,
      αPow_succ']

/-- The `D`-term `D_{k+2}^{p,q}` of the `k`-th iterated couple is the image of
`α^k : D^{p+k,q-k} ⟶ D^{p,q}` (`lem-sp-derived-couple-exact`, claim 4). -/
lemma imageSubobject_αPow (k : ℕ) (a b p q : ℤ) (ha : p + k = a) (hb : b + k = q) :
    imageSubobject (X.αPow k a b p q ha hb) = Subobject.mk (X.ιIter k p q) := by
  rw [← X.αbarIter_ιIter k a b p q ha hb]
  exact Subobject.mk_eq_mk_of_comm _ _
    (image.isoStrongEpiMono (X.αbarIter k a b p q ha hb) (X.ιIter k p q) rfl)
    (image.isoStrongEpiMono_hom_comp_ι _ _ rfl)

lemma isZero_iter_D (k : ℕ) (p q : ℤ) (h : IsZero (X.D p q)) : IsZero ((X.iter k).D p q) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.ιIter k p q)]
  exact h.eq_of_tgt _ _

lemma isZero_iter_E (k : ℕ) (p q : ℤ) (h : IsZero (X.E p q)) : IsZero ((X.iter k).E p q) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ShortComplex.isZero_homology_of_isZero_X₂ _ ih

end ExactCouple

end CategoryTheory
