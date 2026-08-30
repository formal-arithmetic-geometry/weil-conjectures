/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Elements
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Geometric points of the small étale site: the universe of the coefficients, and base change

For a scheme `S : Scheme.{u}`, Mathlib's geometric points `S.pointSmallEtale` have fibre
functors with values in `Type u`, and Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`
applies to a coefficient category concrete over that same `Type u`. The coefficient
categories used in the six functor formalism have `Hom`-types in `Type (u + 1)` and are
concrete over `Type (u + 1)` (this is the case of `ModuleCat.{u + 1} Λ`), so the geometric
points have to be moved up one universe first. This file does that: the family
`AlgebraicGeometry.Scheme.uliftPointSmallEtale` of geometric points at `Type (u + 1)` is
conservative, and hence jointly reflects isomorphisms of `A`-valued étale sheaves.

This file also identifies the geometric points of the small étale site under base change.
Let `f : X ⟶ Y` be a morphism of schemes and let `s : Spec Ω ⟶ X` be a geometric point of
`X`, that is, `Ω` is a separably closed field. Base change along `f` is the functor
`f.Etale : Y.Etale ⥤ X.Etale` between the small étale sites; it is representably flat and
preserves covers, so `CategoryTheory.GrothendieckTopology.Point.comap` turns the geometric
point `AlgebraicGeometry.Scheme.pointSmallEtale s` of `X` into a point of the small étale
site of `Y`. That point is the geometric point `s ≫ f` of `Y`.

On an object `V` of `Y.Etale` the identification is the universal property of the pullback:
a morphism `Spec Ω ⟶ V ×_Y X` over `X` is the same thing as a morphism `Spec Ω ⟶ V` over
`Y`. It is therefore an instance of the adjunction `CategoryTheory.Over.mapPullbackAdj`
between post-composition with `f` and base change along `f` on the slice categories, read
through `CategoryTheory.Adjunction.compCoyonedaIso`.

## Main results

- `AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale`: the
  universe-lifted geometric points of `S` form a conservative family.
- `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`: a morphism of `A`-valued sheaves
  on the small étale site of `S` which is invertible on all these fibres is invertible.

## Main definitions

- `AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso`: the fibre functor of the
  geometric point `s` of `X`, composed with base change along `f`, is the fibre functor of
  the geometric point `s ≫ f` of `Y`.
- `AlgebraicGeometry.Scheme.pointSmallEtaleComapIso`: the point of the small étale site of
  `Y` obtained from `s` by `CategoryTheory.GrothendieckTopology.Point.comap` along base
  change *is* the geometric point `s ≫ f`, as an isomorphism of points.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Ulift

variable (S : Scheme.{u})

/-- The geometric point of the small étale site of `S` at `s`, given by the separable closure
of the residue field of `s`, with its fibre functor taking values in `Type (u + 1)`. -/
noncomputable def uliftPointSmallEtale (s : S) : S.smallEtaleTopology.Point.{u + 1} :=
  (pointSmallEtale ((SpecToEquivOfField (SeparableClosure (S.residueField s)) _).2
    ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s) _)⟩)).ulift.{u + 1}

/-- **The universe-lifted geometric points of `S` form a conservative family.** This is
`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'` moved up one
universe, so that it can be used with coefficients concrete over `Type (u + 1)`. -/
lemma isConservativeFamilyOfPoints_ulift_pointSmallEtale :
    (ObjectProperty.ofObj S.uliftPointSmallEtale).IsConservativeFamilyOfPoints :=
  -- the universes are, in order: the one we lift to, the one of the fibres of
  -- `pointSmallEtale`, and those of the morphisms, the objects and the index type of `S.Etale`
  (isConservativeFamilyOfPoints_pointSmallEtale' S).ulift.{u + 1, u, u, u + 1, u} _

variable (A : Type u') [Category.{u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **The universe-lifted geometric points of `S` jointly reflect isomorphisms of `A`-valued
étale sheaves.** Besides the usual assumptions on the coefficient category `A`, this needs
`A` to be concrete over `Type (u + 1)` in a way compatible with filtered colimits and
sheafification; this holds for `A = ModuleCat.{u + 1} Λ`. -/
lemma jointlyReflectIsomorphisms_ulift_pointSmallEtale :
    JointlyReflectIsomorphisms
      (fun (Φ : (ObjectProperty.ofObj S.uliftPointSmallEtale).FullSubcategory) ↦
        Φ.obj.sheafFiber (A := A)) :=
  (isConservativeFamilyOfPoints_ulift_pointSmallEtale S).jointlyReflectIsomorphisms A

variable {S A}

include hJ in
/-- A morphism of `A`-valued sheaves on the small étale site of `S` whose fibre at every
geometric point of `S` is invertible is invertible. -/
lemma isIso_of_isIso_sheafFiber_map {F G : Sheaf S.smallEtaleTopology A} (φ : F ⟶ G)
    (h : ∀ s : S, IsIso ((S.uliftPointSmallEtale s).sheafFiber.map φ)) :
    IsIso φ :=
  ((jointlyReflectIsomorphisms_ulift_pointSmallEtale S A).isIso_iff φ).2
    (by rintro ⟨-, ⟨s⟩⟩; exact h s)

end Ulift

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- For a geometric point `s : Spec Ω ⟶ X` and a morphism `f : X ⟶ Y`, the fibre functor of
`s` composed with base change along `f` is the fibre functor of the geometric point `s ≫ f`
of `Y`: on `V : Y.Etale` the left hand side is the set of morphisms `Spec Ω ⟶ V ×_Y X` over
`X` and the right hand side is the set of morphisms `Spec Ω ⟶ V` over `Y`, and these agree
by the universal property of the pullback. -/
noncomputable def pointSmallEtaleFiberEtaleIso :
    f.Etale ⋙ (pointSmallEtale s).fiber ≅ (pointSmallEtale (s ≫ f)).fiber :=
  Functor.isoWhiskerLeft (Etale.forget Y)
    ((Adjunction.compCoyonedaIso (CategoryTheory.Over.mapPullbackAdj f)).app
      (op (CategoryTheory.Over.mk s))).symm

/-- The category of elements of the fibre functor of `pointSmallEtale s` composed with base
change is initially small, being equivalent by
`AlgebraicGeometry.Scheme.pointSmallEtaleFiberEtaleIso` to the category of elements of the
fibre functor of `pointSmallEtale (s ≫ f)`. This is the remaining hypothesis of
`CategoryTheory.GrothendieckTopology.Point.comap`. -/
instance initiallySmall_elements_etale_comp_pointSmallEtaleFiber :
    InitiallySmall.{u} (f.Etale ⋙ (pointSmallEtale s).fiber).Elements :=
  initiallySmall_of_initial_of_initiallySmall
    (NatIso.mapElements (pointSmallEtaleFiberEtaleIso f s).symm).functor

/-- Pulling a geometric point `s : Spec Ω ⟶ X` back along base change for a morphism
`f : X ⟶ Y` gives the geometric point `s ≫ f` of `Y`. -/
noncomputable def pointSmallEtaleComapIso :
    (pointSmallEtale s).comap f.Etale (Hom.coverPreserving_etale f) ≅
      pointSmallEtale (s ≫ f) :=
  GrothendieckTopology.Point.isoMk (pointSmallEtaleFiberEtaleIso f s)

end BaseChange

end AlgebraicGeometry.Scheme
