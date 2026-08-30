/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Geometric points of the small étale site at the universe of the coefficients

For a scheme `S : Scheme.{u}`, Mathlib's geometric points `S.pointSmallEtale` have fibre
functors with values in `Type u`, and Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`
applies to a coefficient category concrete over that same `Type u`. The coefficient
categories used in the six functor formalism have `Hom`-types in `Type (u + 1)` and are
concrete over `Type (u + 1)` (this is the case of `ModuleCat.{u + 1} Λ`), so the geometric
points have to be moved up one universe first. This file does that: the family
`AlgebraicGeometry.Scheme.uliftPointSmallEtale` of geometric points at `Type (u + 1)` is
conservative, and hence jointly reflects isomorphisms of `A`-valued étale sheaves.

## Main results

- `AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale`: the
  universe-lifted geometric points of `S` form a conservative family.
- `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`: a morphism of `A`-valued sheaves
  on the small étale site of `S` which is invertible on all these fibres is invertible.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

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

end AlgebraicGeometry.Scheme
