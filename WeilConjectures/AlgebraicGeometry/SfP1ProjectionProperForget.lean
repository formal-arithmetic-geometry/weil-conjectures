/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Projection comparison with fixed ordinary endpoints

.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

namespace SfP1Transport

private theorem whiskered_composite_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) {F R : D ⥤ E} {T : C ⥤ E}
    (h : F ≅ R) (b : T ≅ Q ⋙ R) (K : C) :
    (Functor.isoWhiskerLeft Q h ≪≫ b.symm).hom.app K =
      h.hom.app (Q.obj K) ≫ b.inv.app K := rfl

private theorem projectionComparison_whole
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) (a : Bool) :
    projectionComparison A f i hi a =
      Functor.isoWhiskerLeft (ordinaryFinitePullback A (productMap f i hi))
          (ordinaryProperForgetComparison A (projection f a)) ≪≫
        (properExchange A (projectionSquare f i hi a)).symm := by
  unfold projectionComparison
  rfl

/-- The defining projection comparison, using the canonical proper comparison with
its ordinary endpoint fixed before whiskering, evaluated at any coefficient object.

. -/
theorem projectionComparison_eq_ordinaryProperForget
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) (a : Bool)
    (K : DerivedCategoryModule A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) :
    (projectionComparison A f i hi a).hom.app K =
      (ordinaryProperForgetComparison A (projection f a)).hom.app
          ((ordinaryFinitePullback A (productMap f i hi)).obj K) ≫
        (properExchange A (projectionSquare f i hi a)).inv.app K := by
  calc
    _ = (Functor.isoWhiskerLeft (ordinaryFinitePullback A (productMap f i hi))
          (ordinaryProperForgetComparison A (projection f a)) ≪≫
        (properExchange A (projectionSquare f i hi a)).symm).hom.app K :=
      congrArg (fun e ↦ e.hom.app K) (projectionComparison_whole A f i hi a)
    _ = _ := whiskered_composite_app _ _ _ K

end SfP1Transport
end AlgebraicGeometry.Etale
