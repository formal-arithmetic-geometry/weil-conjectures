/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Composition of right derived functors on bounded below derived categories

This is the bounded below counterpart of
`WeilConjectures.DerivedCategory.RightDerivedFunctor.Comp`. Let `F : C ⥤ D` and
`G : D ⥤ E` be additive functors between abelian categories, with `C` and `D` having
enough injectives. If `F` preserves injective objects, then the canonical comparison

`R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`

is an isomorphism (`Functor.rightDerivedFunctorPlusCompIso`).

## Why this is not a corollary of the unbounded statement

`Functor.rightDerivedFunctorCompIso` in
`WeilConjectures.DerivedCategory.RightDerivedFunctor.Comp` proves the same theorem for the
unbounded derived category, but it assumes `HasKInjectiveResolutions` on both `C` and `D`,
whose only source in this repository is a `sorry`. The bounded below statement needs only
enough injectives, so it rests on proved theorems; see
`WeilConjectures.SixFunctors.Derived` for why that distinction matters here. This file
therefore deliberately does not import anything from
`WeilConjectures.DerivedCategory.GrothendieckAbelian.KInjectiveResolution`.

## The proof, and where it differs from the unbounded one

The shape is the same: the composite `R⁺F ⋙ R⁺G`, equipped with the composite unit
`Functor.rightDerivedFunctorPlusCompUnit`, is itself a right derived functor of
`(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`, and the isomorphism then follows from uniqueness
of right derived functors.

The hypothesis on `F` is where the two arguments part company. The unbounded derivability
structure is indexed by K-injective complexes, so there the requirement is that `F` send
K-injective complexes to K-injective complexes
(`Functor.PreservesKInjectiveComplexes`). The bounded below derivability structure is
indexed by bounded below complexes of *injective objects*, so here the requirement is only
that `F` preserve injective objects — Mathlib's `Functor.PreservesInjectiveObjects`, which
for a right adjoint of a monomorphism-preserving functor is
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`. That is a
weaker and much more readily available hypothesis than the K-injective one, which needs the
left adjoint to be exact.

Concretely, the check that the composite unit is invertible at a bounded below complex `K`
of injectives uses Mathlib's criterion that the unit of a bounded below right derived
functor is invertible at any complex all of whose terms are injective
(the instance in `Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`).
Applied to `G` this is exactly where `F.PreservesInjectiveObjects` enters: the terms of
`F.mapHomotopyCategoryPlus.obj K` are the `F.obj (K.X n)`, injective because `F` preserves
injectives.

## Main definitions

- `CategoryTheory.Functor.rightDerivedFunctorPlusNatTrans` and
  `Functor.rightDerivedFunctorPlusNatIso`: functoriality of the bounded below right derived
  functor in natural transformations of the underived functors.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`: the composition isomorphism
  `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'`: the composition isomorphism
  `R⁺F ⋙ R⁺G ≅ R⁺H` associated with an isomorphism `F ⋙ G ≅ H`. This is the form in which
  the theorem is usually applied, e.g. for the Leray isomorphism.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

namespace Functor

section NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Functoriality of the bounded below right derived functor: a natural transformation
`F ⟶ G` of additive functors induces a natural transformation
`R⁺F ⟶ R⁺G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`. -/
noncomputable def rightDerivedFunctorPlusNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : F.rightDerivedFunctorPlus ⟶ G.rightDerivedFunctorPlus :=
  rightDerivedNatTrans F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ) DerivedCategory.Plus.Qh)

/-- Functoriality of the bounded below right derived functor in natural isomorphisms: an
isomorphism `F ≅ G` of additive functors induces an isomorphism `R⁺F ≅ R⁺G`. -/
noncomputable def rightDerivedFunctorPlusNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) : F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus where
  hom := rightDerivedFunctorPlusNatTrans e.hom
  inv := rightDerivedFunctorPlusNatTrans e.inv
  hom_inv_id := by
    simp [rightDerivedFunctorPlusNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategoryPlus_comp]
  inv_hom_id := by
    simp [rightDerivedFunctorPlusNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategoryPlus_comp]

/-- The natural transformation induced on bounded below right derived functors by a natural
isomorphism is an isomorphism. -/
instance isIso_rightDerivedFunctorPlusNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) [IsIso τ] : IsIso (rightDerivedFunctorPlusNatTrans τ) :=
  inferInstanceAs (IsIso (rightDerivedFunctorPlusNatIso (asIso τ)).hom)

end NatTrans

section Composition

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composite unit exhibiting `R⁺F ⋙ R⁺G` as a candidate right derived functor of
`(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`: it is assembled from the units of `R⁺F` and `R⁺G`
and the composition isomorphism of `mapHomotopyCategoryPlus`. -/
noncomputable def rightDerivedFunctorPlusCompUnit :
    (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- If `F` preserves injective objects, then `R⁺F ⋙ R⁺G`, equipped with the composite unit,
is a right derived functor of `(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`: by the injective
right derivability structure it suffices that the composite unit is an isomorphism on
bounded below complexes of injectives, which holds since the unit of `R⁺F` is an
isomorphism there and the unit of `R⁺G` is an isomorphism on their images under `F`, those
being complexes of injectives again. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp [F.PreservesInjectiveObjects] :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  set K : HomotopyCategory.Plus C := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁
    with hK
  have hKinj : ∀ n : ℤ, Injective (K.obj.as.X n) := fun n => inferInstance
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnit.app K) := inferInstance
  have hFinj : ∀ n : ℤ, Injective ((F.mapHomotopyCategoryPlus.obj K).obj.as.X n) := fun n =>
    inferInstanceAs (Injective (F.obj (K.obj.as.X n)))
  have h₂ : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K)) := by
    have := hFinj
    infer_instance
  dsimp [rightDerivedFunctorPlusCompUnit]
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **Composition of bounded below right derived functors**: for additive functors
`F : C ⥤ D` and `G : D ⥤ E` between abelian categories with enough injectives, where `F`
preserves injective objects, the canonical comparison `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G` is an
isomorphism. -/
noncomputable def rightDerivedFunctorPlusCompIso [F.PreservesInjectiveObjects] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
    (HomotopyCategory.Plus.quasiIso C)

/-- The composition isomorphism `R⁺F ⋙ R⁺G ≅ R⁺H` associated with an isomorphism
`F ⋙ G ≅ H` of additive functors, for `F` preserving injective objects. This is the form in
which the composition theorem is usually applied, e.g. for the Leray isomorphism
`RΓ(Y, R⁺f_* K) ≅ RΓ(X, K)`. -/
noncomputable def rightDerivedFunctorPlusCompIso' {H : C ⥤ E} [H.Additive]
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIso F G).symm ≪≫ rightDerivedFunctorPlusNatIso e

end Composition

end Functor

end CategoryTheory
