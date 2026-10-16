/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple

/-!
# The derived couple of an exact couple

Let `X = (D, E, α, f, g)` be an exact couple of type `s` in an abelian category, with
differential `d = g ∘ f : E^{p,q} ⟶ E^{p+s+2,q-s-1}`. Its *derived couple* `X.derived` is the
exact couple of type `s + 1` with
```
  D'^{p,q} = ker (g : D^{p,q} ⟶ E^{p+s,q-s}) = im (α : D^{p+1,q-1} ⟶ D^{p,q}),
  E'^{p,q} = ker d / im d,
```
`α'` the restriction of `α`, `f'` induced by `f` on cycles of `d` and `g'` characterised by
`g' ∘ ᾱ = [g]`, where `ᾱ : D^{p+1,q-1} ⟶ D'^{p,q}` is the corestriction of `α`.

We take `ker g` rather than `im α` as the definition of `D'`: both are the same subobject of
`D^{p,q}` by exactness, and the kernel avoids reindexing the source of `α`. All exactness
statements are proved by chasing elements up to refinements
(`CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`).

## Main definitions

- `CategoryTheory.ExactCouple.dSc`: the short complex of differentials
  `E^{p-s-2,q+s+1} ⟶ E^{p,q} ⟶ E^{p+s+2,q-s-1}`.
  of differentials.
- `CategoryTheory.ExactCouple.derived`: the derived couple, an exact couple of type `s + 1`
  (`lem-sp-derived-couple-exact`).

## References

* [Stacks Project, Tag 011R](https://stacks.math.columbia.edu/tag/011R)
* [Stacks Project, Tag 0AMJ](https://stacks.math.columbia.edu/tag/0AMJ)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

namespace ExactCouple

variable {C : Type*} [Category* C] [Abelian C] {s : ℕ} (X : ExactCouple C s)

section Reindexing

/-! Lemmas comparing structure maps whose bidegrees agree only propositionally. -/

lemma comp_g_eq_zero_iff {A : C} {p q : ℤ} (x : A ⟶ X.D p q) (p₁ q₁ p₂ q₂ : ℤ)
    (h₁ : p + s = p₁) (h₁' : q₁ + s = q) (h₂ : p + s = p₂) (h₂' : q₂ + s = q) :
    x ≫ X.g p q p₁ q₁ = 0 ↔ x ≫ X.g p q p₂ q₂ = 0 := by
  obtain rfl : p₁ = p₂ := by lia
  obtain rfl : q₁ = q₂ := by lia
  rfl

lemma exists_comp_d_eq {A : C} {a b : ℤ} (x : A ⟶ X.E a b) (a' b' p q : ℤ) (ha : a = a')
    (hb : b = b') (hp : a + s + 2 = p) (hq : q + s + 1 = b) :
    ∃ x' : A ⟶ X.E a' b', x ≫ X.d a b p q = x' ≫ X.d a' b' p q := by
  subst ha hb
  exact ⟨x, rfl⟩

end Reindexing

/-- The short complex `E^{p-s-2,q+s+1} ⟶ E^{p,q} ⟶ E^{p+s+2,q-s-1}` of differentials, whose
homology is the `E`-term of the derived couple. -/
abbrev dSc (p q : ℤ) : ShortComplex C :=
  ShortComplex.mk (X.d (p - s - 2) (q + s + 1) p q) (X.d p q (p + s + 2) (q - s - 1))
    (X.d_d (p - s - 2) (q + s + 1) p q (p + s + 2) (q - s - 1))

/-- The `D`-term `D'^{p,q} = ker (g : D^{p,q} ⟶ E^{p+s,q-s})` of the derived couple; by
exactness it is the image of `α : D^{p+1,q-1} ⟶ D^{p,q}`. -/
noncomputable abbrev D' (p q : ℤ) : C := kernel (X.g p q (p + s) (q - s))

/-- The inclusion `D'^{p,q} ⟶ D^{p,q}`. -/
noncomputable abbrev ι' (p q : ℤ) : X.D' p q ⟶ X.D p q := kernel.ι _

/-- The `E`-term `E'^{p,q} = ker d / im d` of the derived couple. -/
noncomputable abbrev E' (p q : ℤ) : C := (X.dSc p q).homology

@[reassoc (attr := simp)]
lemma ι'_g (p q p' q' : ℤ) (hp : p + s = p' := by lia) (hq : q' + s = q := by lia) :
    X.ι' p q ≫ X.g p q p' q' = 0 :=
  (X.comp_g_eq_zero_iff (X.ι' p q) (p + s) (q - s) p' q' rfl (by lia) hp hq).1
    (kernel.condition _)

/-- The corestriction `ᾱ : D^{p,q} ⟶ D'^{p-1,q+1}` of `α`, an epimorphism. -/
noncomputable def αbar (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) :
    X.D p q ⟶ X.D' p' q' :=
  kernel.lift _ (X.α p q p' q') (X.α_g p q p' q' (p' + s) (q' - s))

@[reassoc (attr := simp)]
lemma αbar_ι' (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) :
    X.αbar p q p' q' ≫ X.ι' p' q' = X.α p q p' q' :=
  kernel.lift_ι _ _ _

instance epi_αbar (p q p' q' : ℤ) (hp : p' + 1 = p) (hq : q + 1 = q') :
    Epi (X.αbar p q p' q' hp hq) :=
  (X.exact_α_g p q p' q' (p' + s) (q' - s)).epi_kernelLift

/-- The restriction `α' : D'^{p,q} ⟶ D'^{p-1,q+1}` of `α`. -/
noncomputable def α' (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) :
    X.D' p q ⟶ X.D' p' q' :=
  kernel.lift _ (X.ι' p q ≫ X.α p q p' q') (by
    rw [assoc, X.α_g p q p' q' (p' + s) (q' - s), comp_zero])

@[reassoc (attr := simp)]
lemma α'_ι' (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) :
    X.α' p q p' q' ≫ X.ι' p' q' = X.ι' p q ≫ X.α p q p' q' :=
  kernel.lift_ι _ _ _

@[reassoc]
lemma αbar_α' (p q p' q' p'' q'' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia)
    (hp' : p'' + 1 = p' := by lia) (hq' : q' + 1 = q'' := by lia) :
    X.αbar p q p' q' ≫ X.α' p' q' p'' q'' = X.α p q p' q' ≫ X.αbar p' q' p'' q'' := by
  rw [← cancel_mono (X.ι' p'' q''), assoc, X.α'_ι' p' q' p'' q'', X.αbar_ι'_assoc p q p' q',
    assoc, X.αbar_ι' p' q' p'' q'']

/-- `f` restricted to the cycles of `d` lands in `D' = ker g`. -/
noncomputable def fCycles (p q p' q' : ℤ) (hp : p + 2 = p' := by lia)
    (hq : q' + 1 = q := by lia) : (X.dSc p q).cycles ⟶ X.D' p' q' :=
  kernel.lift _ ((X.dSc p q).iCycles ≫ X.f p q p' q') (by
    refine (X.comp_g_eq_zero_iff _ (p' + s) (q' - s) (p + s + 2) (q - s - 1) rfl (by lia)
      (by lia) (by lia)).2 ?_
    rw [assoc, ← X.d_eq p q (p + s + 2) (q - s - 1) p' q']
    exact (X.dSc p q).iCycles_g)

@[reassoc (attr := simp)]
lemma fCycles_ι' (p q p' q' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia) :
    X.fCycles p q p' q' ≫ X.ι' p' q' = (X.dSc p q).iCycles ≫ X.f p q p' q' :=
  kernel.lift_ι _ _ _

/-- The map `f' : E'^{p,q} ⟶ D'^{p+2,q-1}` induced by `f`. -/
noncomputable def f' (p q p' q' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia) :
    X.E' p q ⟶ X.D' p' q' :=
  (X.dSc p q).descHomology (X.fCycles p q p' q') (by
    rw [← cancel_mono (X.ι' p' q'), assoc, X.fCycles_ι' p q p' q', zero_comp, ← assoc,
      (X.dSc p q).toCycles_i]
    change X.d (p - s - 2) (q + s + 1) p q ≫ X.f p q p' q' = 0
    dsimp only [d]
    rw [assoc, X.g_f (p - s - 2 + 2) (q + s + 1 - 1) p q p' q', comp_zero])

@[reassoc (attr := simp)]
lemma π_f' (p q p' q' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia) :
    (X.dSc p q).homologyπ ≫ X.f' p q p' q' = X.fCycles p q p' q' :=
  (X.dSc p q).π_descHomology _ _

/-- `g` corestricted to the cycles of `d`. -/
noncomputable def gCycles (p q p' q' : ℤ) (hp : p + s = p' := by lia)
    (hq : q' + s = q := by lia) : X.D p q ⟶ (X.dSc p' q').cycles :=
  (X.dSc p' q').liftCycles (X.g p q p' q') (by
    change X.g p q p' q' ≫ X.d p' q' (p' + s + 2) (q' - s - 1) = 0
    dsimp only [d]
    rw [X.g_f_assoc p q p' q' (p' + 2) (q' - 1), zero_comp])

@[reassoc (attr := simp)]
lemma gCycles_i (p q p' q' : ℤ) (hp : p + s = p' := by lia) (hq : q' + s = q := by lia) :
    X.gCycles p q p' q' ≫ (X.dSc p' q').iCycles = X.g p q p' q' :=
  (X.dSc p' q').liftCycles_i _ _

lemma comp_gCycles {A : C} (p q p' q' : ℤ) (y : A ⟶ X.D p q) (hp : p + s = p' := by lia)
    (hq : q' + s = q := by lia) :
    y ≫ X.gCycles p q p' q' = (X.dSc p' q').liftCycles (y ≫ X.g p q p' q') (by
      rw [assoc, ← X.gCycles_i p q p' q', assoc, ShortComplex.iCycles_g, comp_zero,
        comp_zero]) := by
  rw [gCycles, ShortComplex.comp_liftCycles]

/-- If `y = x ∘ d` is a boundary, then its class in `E'` vanishes. The source of the
differential may be indexed by any pair of integers equal to `(p - s - 2, q + s + 1)`. -/
lemma liftCycles_homologyπ_eq_zero {A : C} (p q : ℤ) (y : A ⟶ X.E p q)
    (hy : y ≫ (X.dSc p q).g = 0) (a b : ℤ) (x : A ⟶ X.E a b) (hab : a + s + 2 = p)
    (hab' : q + s + 1 = b) (h : y = x ≫ X.d a b p q) :
    (X.dSc p q).liftCycles y hy ≫ (X.dSc p q).homologyπ = 0 := by
  obtain ⟨x', hx'⟩ :=
    X.exists_comp_d_eq x (p - s - 2) (q + s + 1) p q (by lia) (by lia) hab hab'
  exact (X.dSc p q).liftCycles_homologyπ_eq_zero_of_boundary y x' (h.trans hx')

lemma kernel_ι_αbar_gCycles_homologyπ (p q p' q' : ℤ) (hp : p + (s + 1 : ℕ) = p')
    (hq : q' + (s + 1 : ℕ) = q) :
    kernel.ι (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1)) ≫
      X.gCycles (p + 1) (q - 1) p' q' ≫
      (X.dSc p' q').homologyπ = 0 := by
  set k := kernel.ι (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1))
  have hk : k ≫ X.α (p + 1) (q - 1) p q = 0 := by
    rw [← X.αbar_ι' (p + 1) (q - 1) p q, kernel.condition_assoc, zero_comp]
  obtain ⟨A', π, hπ, x, hx⟩ :=
    (X.exact_f_α (p - 1) q (p + 1) (q - 1) p q).exact_up_to_refinements k hk
  dsimp at hx
  rw [← cancel_epi π, comp_zero, ← assoc, ← assoc, X.comp_gCycles (p + 1) (q - 1) p' q']
  exact X.liftCycles_homologyπ_eq_zero p' q' _ _ (p - 1) q x (by push_cast at hp; lia)
    (by push_cast at hq; lia) (by rw [hx, assoc, ← X.d_eq (p - 1) q p' q' (p + 1) (q - 1)])

/-- The map `g' : D'^{p,q} ⟶ E'^{p+s+1,q-s-1}`, characterised by `g' ∘ ᾱ = [g]`
(`CategoryTheory.ExactCouple.αbar_g'`). -/
noncomputable def g' (p q p' q' : ℤ) (hp : p + (s + 1 : ℕ) = p' := by lia)
    (hq : q' + (s + 1 : ℕ) = q := by lia) : X.D' p q ⟶ X.E' p' q' :=
  Abelian.epiDesc (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1))
    (X.gCycles (p + 1) (q - 1) p' q' (by push_cast at hp; lia) (by push_cast at hq; lia) ≫
      (X.dSc p' q').homologyπ) (X.kernel_ι_αbar_gCycles_homologyπ p q p' q' hp hq)

@[reassoc (attr := simp)]
lemma αbar_g' (a b p q p' q' : ℤ) (ha : p + 1 = a := by lia) (hb : b + 1 = q := by lia)
    (hp : p + (s + 1 : ℕ) = p' := by lia) (hq : q' + (s + 1 : ℕ) = q := by lia) :
    X.αbar a b p q ≫ X.g' p q p' q' =
      X.gCycles a b p' q' (by push_cast at hp; lia) (by push_cast at hq; lia) ≫
        (X.dSc p' q').homologyπ := by
  obtain rfl : a = p + 1 := by lia
  obtain rfl : b = q - 1 := by lia
  exact Abelian.comp_epiDesc (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1)) _ _

/-! ### The derived couple is exact -/

@[reassoc (attr := simp)]
lemma f'_α' (a b p q p' q' : ℤ) (hp : a + 2 = p := by lia) (hq : q + 1 = b := by lia)
    (hp' : p' + 1 = p := by lia) (hq' : q + 1 = q' := by lia) :
    X.f' a b p q ≫ X.α' p q p' q' = 0 := by
  rw [← cancel_epi (X.dSc a b).homologyπ, ← cancel_mono (X.ι' p' q')]
  simp only [assoc, comp_zero, zero_comp]
  rw [X.α'_ι' p q p' q', X.π_f'_assoc a b p q, X.fCycles_ι'_assoc a b p q,
    X.f_α a b p q p' q', comp_zero]

@[reassoc (attr := simp)]
lemma g'_f' (p₀ q₀ p q p' q' : ℤ) (hp : p₀ + (s + 1 : ℕ) = p := by lia)
    (hq : q + (s + 1 : ℕ) = q₀ := by lia) (hp' : p + 2 = p' := by lia)
    (hq' : q' + 1 = q := by lia) :
    X.g' p₀ q₀ p q ≫ X.f' p q p' q' = 0 := by
  rw [← cancel_epi (X.αbar (p₀ + 1) (q₀ - 1) p₀ q₀ rfl (sub_add_cancel q₀ 1)),
    ← cancel_mono (X.ι' p' q')]
  simp only [assoc, comp_zero, zero_comp]
  rw [X.αbar_g'_assoc (p₀ + 1) (q₀ - 1) p₀ q₀ p q, X.π_f'_assoc p q p' q',
    X.fCycles_ι' p q p' q', X.gCycles_i_assoc (p₀ + 1) (q₀ - 1) p q,
    X.g_f (p₀ + 1) (q₀ - 1) p q p' q']

@[reassoc (attr := simp)]
lemma α'_g' (p q p' q' p'' q'' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia)
    (hp' : p' + (s + 1 : ℕ) = p'' := by lia) (hq' : q'' + (s + 1 : ℕ) = q' := by lia) :
    X.α' p q p' q' ≫ X.g' p' q' p'' q'' = 0 := by
  rw [← cancel_epi (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1)), comp_zero,
    X.αbar_α'_assoc (p + 1) (q - 1) p q p' q', X.αbar_g' p q p' q' p'' q'', ← assoc,
    X.comp_gCycles p q p'' q'']
  exact X.liftCycles_homologyπ_eq_zero p'' q'' _ _ (p'' - s - 2) (q'' + s + 1) 0 (by lia)
    (by lia) (by rw [X.α_g (p + 1) (q - 1) p q p'' q'', zero_comp])

lemma exact_f'_α' (a b p q p' q' : ℤ) (hp : a + 2 = p := by lia) (hq : q + 1 = b := by lia)
    (hp' : p' + 1 = p := by lia) (hq' : q + 1 = q' := by lia) :
    (ShortComplex.mk _ _ (X.f'_α' a b p q p' q')).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A y hy
  dsimp at y hy ⊢
  have hy' : (y ≫ X.ι' p q) ≫ X.α p q p' q' = 0 := by
    rw [assoc, ← X.α'_ι' p q p' q', ← assoc, hy, zero_comp]
  obtain ⟨A₁, π₁, hπ₁, x, hx⟩ :=
    (X.exact_f_α a b p q p' q').exact_up_to_refinements (y ≫ X.ι' p q) hy'
  dsimp at hx
  have hxd : x ≫ (X.dSc a b).g = 0 := by
    change x ≫ X.d a b (a + s + 2) (b - s - 1) = 0
    rw [X.d_eq a b (a + s + 2) (b - s - 1) p q, ← assoc, ← hx,
      X.comp_g_eq_zero_iff _ (a + s + 2) (b - s - 1) (p + s) (q - s) (by lia) (by lia) rfl
        (by lia), assoc, assoc, X.ι'_g p q (p + s) (q - s), comp_zero, comp_zero]
  refine ⟨A₁, π₁, hπ₁, (X.dSc a b).liftCycles x hxd ≫ (X.dSc a b).homologyπ, ?_⟩
  rw [← cancel_mono (X.ι' p q)]
  simp only [assoc]
  rw [hx, X.π_f'_assoc a b p q, X.fCycles_ι' a b p q, (X.dSc a b).liftCycles_i_assoc]

lemma exact_g'_f' (p₀ q₀ p q p' q' : ℤ) (hp : p₀ + (s + 1 : ℕ) = p := by lia)
    (hq : q + (s + 1 : ℕ) = q₀ := by lia) (hp' : p + 2 = p' := by lia)
    (hq' : q' + 1 = q := by lia) :
    (ShortComplex.mk _ _ (X.g'_f' p₀ q₀ p q p' q')).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A e he
  dsimp at e he ⊢
  obtain ⟨A₁, π₁, hπ₁, z, hz⟩ :=
    surjective_up_to_refinements_of_epi (X.dSc p q).homologyπ e
  have hz' : (z ≫ (X.dSc p q).iCycles) ≫ X.f p q p' q' = 0 := by
    rw [assoc, ← X.fCycles_ι' p q p' q', ← X.π_f'_assoc p q p' q', ← assoc z, ← hz, assoc,
      reassoc_of% he, zero_comp, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, w, hw⟩ :=
    (X.exact_g_f (p₀ + 1) (q₀ - 1) p q p' q').exact_up_to_refinements _ hz'
  dsimp at hw
  refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _,
    w ≫ X.αbar (p₀ + 1) (q₀ - 1) p₀ q₀ rfl (sub_add_cancel q₀ 1), ?_⟩
  have : π₂ ≫ z = w ≫ X.gCycles (p₀ + 1) (q₀ - 1) p q := by
    rw [← cancel_mono (X.dSc p q).iCycles, assoc, hw, assoc,
      X.gCycles_i (p₀ + 1) (q₀ - 1) p q]
  simp only [assoc]
  rw [hz, X.αbar_g' (p₀ + 1) (q₀ - 1) p₀ q₀ p q, ← assoc π₂ z, this, assoc]

lemma exact_α'_g' (p q p' q' p'' q'' : ℤ) (hp : p' + 1 = p := by lia)
    (hq : q + 1 = q' := by lia) (hp' : p' + (s + 1 : ℕ) = p'' := by lia)
    (hq' : q'' + (s + 1 : ℕ) = q' := by lia) :
    (ShortComplex.mk _ _ (X.α'_g' p q p' q' p'' q'')).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A y hy
  dsimp at y hy ⊢
  obtain ⟨A₁, π₁, hπ₁, y', hy'⟩ :=
    surjective_up_to_refinements_of_epi (X.αbar p q p' q' hp hq) y
  have h₀ : y' ≫ X.gCycles p q p'' q'' ≫ (X.dSc p'' q'').homologyπ = 0 := by
    rw [← X.αbar_g' p q p' q' p'' q'', ← assoc, ← hy', assoc, hy, comp_zero]
  rw [← assoc, X.comp_gCycles p q p'' q''] at h₀
  obtain ⟨A₂, π₂, hπ₂, x, hx⟩ :=
    ((X.dSc p'' q'').liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _).1 h₀
  obtain ⟨x', hx'⟩ := X.exists_comp_d_eq x (p - 2) (q + 1) p'' q'' (by lia) (by lia) (by lia)
    (by lia)
  have h₁ : (π₂ ≫ y' - x' ≫ X.f (p - 2) (q + 1) p q) ≫ X.g p q p'' q'' = 0 := by
    rw [sub_comp, assoc, assoc, ← X.d_eq (p - 2) (q + 1) p'' q'' p q, ← hx', sub_eq_zero]
    exact hx
  obtain ⟨A₃, π₃, hπ₃, z, hz⟩ :=
    (X.exact_α_g (p + 1) (q - 1) p q p'' q'').exact_up_to_refinements _ h₁
  dsimp at hz
  refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance,
    z ≫ X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1), ?_⟩
  have e₁ : π₁ ≫ y ≫ X.ι' p' q' = y' ≫ X.α p q p' q' := by
    rw [← assoc, hy', assoc, X.αbar_ι' p q p' q']
  rw [← cancel_mono (X.ι' p' q')]
  simp only [assoc]
  rw [e₁, X.α'_ι' p q p' q', X.αbar_ι'_assoc (p + 1) (q - 1) p q, ← reassoc_of% hz,
    sub_comp, assoc, assoc, X.f_α (p - 2) (q + 1) p q p' q', comp_zero, sub_zero]

/-- The derived couple of an exact couple of type `s`: an exact couple of type `s + 1` with
`D'^{p,q} = ker g = im α ⊆ D^{p,q}` and `E'^{p,q} = ker d / im d`, `α'` the restriction of `α`,
`f'` induced by `f` and `g'` given by `g' ∘ ᾱ = [g]`.

This is blueprint `lem-sp-derived-couple-exact` (claims 2 and 3). -/
@[simps]
noncomputable def derived : ExactCouple C (s + 1) where
  D := X.D'
  E := X.E'
  α p q p' q' _ _ := X.α' p q p' q'
  f p q p' q' _ _ := X.f' p q p' q'
  g p q p' q' _ _ := X.g' p q p' q'
  f_α a b p q p' q' _ _ _ _ := X.f'_α' a b p q p' q'
  g_f p₀ q₀ p q p' q' _ _ _ _ := X.g'_f' p₀ q₀ p q p' q'
  α_g p q p' q' p'' q'' _ _ _ _ := X.α'_g' p q p' q' p'' q''
  exact_f_α a b p q p' q' _ _ _ _ := X.exact_f'_α' a b p q p' q'
  exact_g_f p₀ q₀ p q p' q' _ _ _ _ := X.exact_g'_f' p₀ q₀ p q p' q'
  exact_α_g p q p' q' p'' q'' _ _ _ _ := X.exact_α'_g' p q p' q' p'' q''

end ExactCouple

end CategoryTheory
