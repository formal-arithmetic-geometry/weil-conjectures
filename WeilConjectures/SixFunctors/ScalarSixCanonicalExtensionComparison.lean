/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison

/-! # Scalar change commutes with the canonical image-factorization extension.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-canonical-extension-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exactPushTransport.{v, w}
    {A B C D : Type w}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [hK : Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (P : C ⥤ D) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : A ≌ C) (h : B ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [h.functor.Additive] [h.inverse.Additive]
    (r : F ⋙ h.functor ≅ e.functor ⋙ P) :
    Nonempty (F.rightDerivedFunctor ≅
      e.functor.mapDerivedCategory ⋙ P.mapDerivedCategory ⋙ h.inverse.mapDerivedCategory) := by
  let q := r.isoCompInverse (H := h)
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso q.symm
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso q.symm
  let d : F.mapDerivedCategory ⋙ h.mapDerivedCategory.functor ≅
      e.mapDerivedCategory.functor ⋙ P.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso F h.functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso r ≪≫
      Functor.mapDerivedCategoryCompIso e.functor P
  exact ⟨F.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    d.isoCompInverse (H := h.mapDerivedCategory) ≪≫ Functor.associator _ _ _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
