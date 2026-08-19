/-
Copyright (c) 2026 Weil Conjectures Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures Contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Étale neighbourhoods, and shrinking them to the image

For a morphism of schemes `g : Z ⟶ Y` and `V : Z.Etale`, the comma category
`StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)` indexes the colimits
computing the left Kan extension along the opposite of base change, hence the pullback
`g^*` on small étale sites. This file identifies that comma category geometrically and
proves the one shrinking operation available in it.

## The identification

`Etale.overPullbackHomEquiv` says that a morphism `V ⟶ (Over.pullback @Etale ⊤ g).obj W`
in `Z.Etale` is the same thing as a `Y`-morphism `V.left ⟶ W.left`, where `V.left` is a
`Y`-scheme via `V.hom ≫ g`. So an object of the comma category is a pair consisting of a
scheme `W` étale over `Y` and a `Y`-morphism `V.left ⟶ W.left`: an **étale neighbourhood**
of the `Y`-scheme `(V.left, V.hom ≫ g)`, in the sense of SGA 4 VIII. For étale `g` the
neighbourhood `(V.left, 𝟙)` is initial, which is why base change along an étale morphism
needs no smallness argument at all.

## Shrinking

The comma category is *not* essentially small — `∐ (i : I) Y` is étale over `Y`, and these
are pairwise non-isomorphic for non-equinumerous `I`, so the colimits indexed by it cannot
come from smallness of the index category. What is available instead is that a neighbourhood
may be shrunk to any open of `W.left` containing the image of `V.left`:
`Etale.restrict` builds the shrunk neighbourhood and `Etale.restrictHomTo` is the resulting
morphism in the comma category. Choosing an affine open around the image of each point of
`V.left` and taking their union, every neighbourhood is reached from one that is covered by
affine opens indexed by the points of `V.left` — `Etale.IsBounded` — which is
`Etale.exists_isBounded_and_nonempty_hom`.

That is exactly the weak-initiality hypothesis of
`CategoryTheory.initiallySmall_of_small_weakly_initial_set`, whose other hypothesis,
cofilteredness, holds because base change preserves the finite limits of the small étale
site. Assembling the two gives `Etale.initiallySmall_structuredArrow_overPullback_of_small`,
which reduces the whole obligation to a single statement with no category theory in it:

> **`Small.{u}` of the `V`-bounded objects** — up to isomorphism there is only a `u`-small
> family of schemes étale over `Y` admitting an open cover, indexed by a fixed `u`-small
> type, by affine opens.

That statement is **not** proved here, and is the entire remaining mathematical content
behind the base-change Kan extensions of
`WeilConjectures/CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean`. Once it is
available, `InitiallySmall` yields the colimits and their exactness by Mathlib's
`FinallySmall` machinery, with no further hypothesis on the coefficient category: a
Grothendieck abelian category has colimits of size `u` and they are exact.

Two other candidate weakly initial families are refuted rather than supported by the
description above, and both failures are visible in the language this file sets up:

* the neighbourhoods with `W` affine — `V.left` need not be quasi-compact, so the image of
  `V.left` need not lie in a single affine open;
* the neighbourhoods whose centre `V.left ⟶ W.left` is surjective — that morphism is a
  morphism of `Y`-schemes and is *not* étale (`V.left` is étale over `Z`, not over `Y`), so
  its image need not be open and the shrinking step is unavailable for it.

## Main definitions and results

- `AlgebraicGeometry.Etale.overPullbackHomEquiv`: the identification of the comma category
  with the category of étale neighbourhoods.
- `AlgebraicGeometry.Etale.restrict`: an open subscheme of a scheme étale over `Y` is again
  étale over `Y`.
- `AlgebraicGeometry.Etale.structuredArrowMk`: the object of the comma category attached to
  an étale neighbourhood.
- `AlgebraicGeometry.Etale.structuredArrowRestrictHom` and
  `AlgebraicGeometry.Etale.restrictHomTo`: shrinking a neighbourhood to an open containing
  the image of its centre gives a morphism in the comma category.
- `AlgebraicGeometry.Etale.exists_isAffineOpen_iSup_range_subset`: the image of a morphism of
  schemes is contained in a supremum of affine opens indexed by the points of the source.
- `AlgebraicGeometry.Etale.IsBounded` and
  `AlgebraicGeometry.Etale.exists_isBounded_and_nonempty_hom`: the objects covered by affine
  opens indexed by the points of `V.left` are weakly initial.
- `AlgebraicGeometry.Etale.initiallySmall_structuredArrow_overPullback_of_small`: hence the
  comma category is `u`-initially small as soon as those objects form a `u`-small family.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

section HomEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The comma category of base change is the category of étale neighbourhoods.**

A morphism `V ⟶ (Over.pullback @Etale ⊤ g).obj W` in `Z.Etale` is the same thing as a
morphism `V.left ⟶ W.left` making `V.left` a `Y`-scheme over `W.left` via `V.hom ≫ g`. -/
noncomputable def overPullbackHomEquiv (V : Z.Etale) (W : Y.Etale) :
    (V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W) ≃
      { a : V.left ⟶ W.left // a ≫ W.hom = V.hom ≫ g } where
  toFun φ := ⟨φ.left ≫ pullback.fst W.hom g, by
    have h : φ.left ≫ pullback.snd W.hom g = V.hom := MorphismProperty.Over.w φ
    have hc : pullback.fst W.hom g ≫ W.hom = pullback.snd W.hom g ≫ g := pullback.condition
    rw [Category.assoc, hc, ← Category.assoc, h]⟩
  invFun a := MorphismProperty.Over.homMk
      (pullback.lift a.1 V.hom a.2) (pullback.lift_snd _ _ _) trivial
  left_inv φ := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift _ _ _ = φ.left
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (MorphismProperty.Over.w φ).symm
  right_inv a := by
    apply Subtype.ext
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma overPullbackHomEquiv_apply_coe (V : Z.Etale) (W : Y.Etale)
    (φ : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W) :
    (overPullbackHomEquiv g V W φ).1 = φ.left ≫ pullback.fst W.hom g :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma overPullbackHomEquiv_symm_apply_left (V : Z.Etale) (W : Y.Etale)
    (a : { a : V.left ⟶ W.left // a ≫ W.hom = V.hom ≫ g }) :
    ((overPullbackHomEquiv g V W).symm a).left = pullback.lift a.1 V.hom a.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identification of `Etale.overPullbackHomEquiv` is natural in the neighbourhood: it
turns composition in the comma category into composition of `Y`-morphisms. -/
lemma overPullbackHomEquiv_comp_map (V : Z.Etale) {W W' : Y.Etale}
    (φ : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W) (ψ : W ⟶ W') :
    (overPullbackHomEquiv g V W' (φ ≫ (MorphismProperty.Over.pullback @Etale ⊤ g).map ψ)).1 =
      (overPullbackHomEquiv g V W φ).1 ≫ ψ.left := by
  have h : ((MorphismProperty.Over.pullback @Etale ⊤ g).map ψ).left ≫ pullback.fst W'.hom g =
      pullback.fst W.hom g ≫ ψ.left := pullback.lift_fst _ _ _
  change (φ ≫ _).left ≫ _ = _
  rw [MorphismProperty.Comma.comp_left, Category.assoc, h, overPullbackHomEquiv_apply_coe,
    Category.assoc]

end HomEquiv

section Restrict

/-- An open subscheme of a scheme étale over `Y` is again a scheme étale over `Y`. -/
abbrev restrict (W : Y.Etale) (U : W.left.Opens) : Y.Etale :=
  Scheme.Etale.mk (U.ι ≫ W.hom)

/-- The open immersion `W ∣_ U ⟶ W` as a morphism of schemes étale over `Y`. -/
def restrictHom (W : Y.Etale) (U : W.left.Opens) : restrict W U ⟶ W :=
  MorphismProperty.Over.homMk U.ι rfl trivial

@[simp]
lemma restrictHom_left (W : Y.Etale) (U : W.left.Opens) :
    (restrictHom W U).left = U.ι :=
  rfl

/-- The lift of a morphism of schemes through the open immersion of an open containing its
image, as a morphism into the open subscheme. -/
noncomputable def liftOpens {V W : Scheme.{u}} (a : V ⟶ W) (U : W.Opens)
    (hU : Set.range a.base ⊆ U) : V ⟶ U :=
  IsOpenImmersion.lift U.ι a (hU.trans (Scheme.Opens.range_ι U).ge)

@[reassoc (attr := simp)]
lemma liftOpens_ι {V W : Scheme.{u}} (a : V ⟶ W) (U : W.Opens) (hU : Set.range a.base ⊆ U) :
    liftOpens a U hU ≫ U.ι = a :=
  IsOpenImmersion.lift_fac _ _ _

/-- Shrinking preserves the structure of a `Y`-morphism: if `a : V.left ⟶ W.left` is a
`Y`-morphism, so is its lift into an open `U` containing the image of `a`. -/
lemma liftOpens_restrict_hom (V : Z.Etale) (W : Y.Etale) (a : V.left ⟶ W.left)
    (ha : a ≫ W.hom = V.hom ≫ g) (U : W.left.Opens) (hU : Set.range a.base ⊆ U) :
    liftOpens a U hU ≫ (restrict W U).hom = V.hom ≫ g := by
  change liftOpens a U hU ≫ U.ι ≫ W.hom = _
  rw [← Category.assoc, liftOpens_ι]
  exact ha

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The object of the comma category attached to an étale neighbourhood `(W, a)` of the
`Y`-scheme `(V.left, V.hom ≫ g)`. -/
noncomputable def structuredArrowMk (V : Z.Etale) (W : Y.Etale) (a : V.left ⟶ W.left)
    (ha : a ≫ W.hom = V.hom ≫ g) :
    StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g) :=
  StructuredArrow.mk ((overPullbackHomEquiv g V W).symm ⟨a, ha⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma structuredArrowMk_right (V : Z.Etale) (W : Y.Etale) (a : V.left ⟶ W.left)
    (ha : a ≫ W.hom = V.hom ≫ g) :
    (structuredArrowMk g V W a ha).right = W :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Shrinking an étale neighbourhood to an open containing the image.**

If the image of `a : V.left ⟶ W.left` is contained in an open `U` of `W.left`, then the
étale neighbourhood `(W, a)` receives a morphism from the étale neighbourhood
`(W ∣_ U, a')`, where `a'` is the lift of `a` through the open immersion `U.ι`. -/
noncomputable def structuredArrowRestrictHom (V : Z.Etale) (W : Y.Etale) (a : V.left ⟶ W.left)
    (ha : a ≫ W.hom = V.hom ≫ g) (U : W.left.Opens) (hU : Set.range a.base ⊆ U) :
    structuredArrowMk g V (restrict W U) (liftOpens a U hU)
        (liftOpens_restrict_hom g V W a ha U hU) ⟶
      structuredArrowMk g V W a ha :=
  StructuredArrow.homMk (restrictHom W U) (by
    change (overPullbackHomEquiv g V (restrict W U)).symm
          ⟨liftOpens a U hU, liftOpens_restrict_hom g V W a ha U hU⟩ ≫
        (MorphismProperty.Over.pullback @Etale ⊤ g).map (restrictHom W U) =
      (overPullbackHomEquiv g V W).symm ⟨a, ha⟩
    apply (overPullbackHomEquiv g V W).injective
    apply Subtype.ext
    rw [overPullbackHomEquiv_comp_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      restrictHom_left]
    exact liftOpens_ι a U hU)

end Restrict

section AffineCover

/-- The `Y`-morphism `V.left ⟶ T.right.left` underlying an object `T` of the comma category:
the "centre" of the étale neighbourhood `T`. -/
noncomputable abbrev arrow (V : Z.Etale)
    (T : StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) :
    V.left ⟶ T.right.left :=
  (overPullbackHomEquiv g V T.right T.hom).1

lemma arrow_comp (V : Z.Etale)
    (T : StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) :
    arrow g V T ≫ T.right.hom = V.hom ≫ g :=
  (overPullbackHomEquiv g V T.right T.hom).2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Etale.structuredArrowRestrictHom` for an arbitrary object of the comma category: every
étale neighbourhood receives a morphism from its restriction to any open containing the image
of its centre. -/
noncomputable def restrictHomTo (V : Z.Etale)
    (T : StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g))
    (U : T.right.left.Opens) (hU : Set.range (arrow g V T).base ⊆ U) :
    structuredArrowMk g V (restrict T.right U) (liftOpens (arrow g V T) U hU)
        (liftOpens_restrict_hom g V T.right _ (arrow_comp g V T) U hU) ⟶ T :=
  StructuredArrow.homMk (restrictHom T.right U) (by
    change (overPullbackHomEquiv g V (restrict T.right U)).symm
        ⟨liftOpens (arrow g V T) U hU,
          liftOpens_restrict_hom g V T.right _ (arrow_comp g V T) U hU⟩ ≫
      (MorphismProperty.Over.pullback @Etale ⊤ g).map (restrictHom T.right U) = T.hom
    apply (overPullbackHomEquiv g V T.right).injective
    apply Subtype.ext
    rw [overPullbackHomEquiv_comp_map, Equiv.apply_symm_apply, restrictHom_left]
    exact liftOpens_ι (arrow g V T) U hU)

/-- The image of a morphism of schemes is contained in a supremum of affine opens indexed by
the points of the source: choose an affine open neighbourhood of the image of each point.

This is the bound behind the shrinking step: it produces an open covered by at most `#V`
affine opens, and the carrier of a scheme in `Scheme.{u}` is a type in `Type u`. -/
theorem exists_isAffineOpen_iSup_range_subset {V W : Scheme.{u}} (a : V ⟶ W) :
    ∃ O : V → W.Opens, (∀ x, IsAffineOpen (O x)) ∧ (∀ x, a.base x ∈ O x) ∧
      Set.range a.base ⊆ (⨆ x, O x : W.Opens) := by
  choose O hO hmem _ using fun x : V ↦
    exists_isAffineOpen_mem_and_subset (X := W) (x := a.base x) (U := ⊤) trivial
  refine ⟨O, hO, hmem, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hmem x⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An object of the comma category is **`V`-bounded** if its underlying scheme is covered by
affine opens indexed by the points of `V.left`.

This is the boundedness that survives the two refuted candidate families: the `V`-bounded
objects are weakly initial (`Etale.exists_isBounded_and_nonempty_hom`), whereas neither the
affine objects nor the objects with surjective centre are. -/
def IsBounded (V : Z.Etale)
    (T : StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) : Prop :=
  ∃ O : V.left → T.right.left.Opens, (∀ x, IsAffineOpen (O x)) ∧ ⨆ x, O x = ⊤

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The `V`-bounded étale neighbourhoods are weakly initial.**

Every object of `StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)` receives a
morphism from a `V`-bounded one: shrink it to a union of affine open neighbourhoods of the
images of the points of `V.left`.

Together with `Etale.representablyFlat_overPullback` — which makes the comma category
cofiltered — this is one of the two inputs of
`CategoryTheory.initiallySmall_of_small_weakly_initial_set`. The other,
`Small.{u}` of the `V`-bounded objects, is **not** proved here and is the remaining
mathematical content behind the base-change Kan extensions. -/
theorem exists_isBounded_and_nonempty_hom (V : Z.Etale)
    (T : StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) :
    ∃ S, IsBounded g V S ∧ Nonempty (S ⟶ T) := by
  obtain ⟨O, hO, -, hsub⟩ := exists_isAffineOpen_iSup_range_subset (arrow g V T)
  refine ⟨_, ⟨fun x ↦ (⨆ x, O x : T.right.left.Opens).ι ⁻¹ᵁ O x, fun x ↦ ?_, ?_⟩,
    ⟨restrictHomTo g V T _ hsub⟩⟩
  · refine (hO x).preimage_of_isOpenImmersion _ ?_
    rw [Scheme.Opens.opensRange_ι]
    exact le_iSup O x
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 y.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The reduction: one `Small.{u}` statement is all that is missing.**

If the `V`-bounded étale neighbourhoods form a `u`-small family, then the comma category
indexing the base-change Kan extensions is `u`-initially small, hence — since a Grothendieck
abelian category has colimits of size `u` and they are exact — the colimits computing those
Kan extensions exist and are left exact.

The two inputs are supplied here and on `master`: weak initiality is
`Etale.exists_isBounded_and_nonempty_hom`, and cofilteredness is representable flatness of
base change, which holds because the small étale site is finitely complete and base change
preserves finite limits. Only the smallness is open.

The hypothesis is deliberately a plain argument rather than an instance: it is unproved, and
an instance would let it be discharged silently. -/
theorem initiallySmall_structuredArrow_overPullback_of_small (V : Z.Etale)
    (h : Small.{u} ↥{T : StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g) |
      IsBounded g V T}) :
    InitiallySmall.{u} (StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) := by
  haveI : RepresentablyFlat (MorphismProperty.Over.pullback @Etale ⊤ g) :=
    flat_of_preservesFiniteLimits _
  haveI : IsCofiltered (StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) :=
    RepresentablyFlat.cofiltered (F := MorphismProperty.Over.pullback @Etale ⊤ g) V
  haveI := h
  exact initiallySmall_of_small_weakly_initial_set {T | IsBounded g V T}
    fun T ↦ exists_isBounded_and_nonempty_hom g V T

end AffineCover

end AlgebraicGeometry.Etale
