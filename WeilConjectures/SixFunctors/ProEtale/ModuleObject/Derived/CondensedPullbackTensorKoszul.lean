/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Derived pullback compatibility with the Koszul braiding

The canonical pullback comparison equals the generic left-derived tensor comparison.
The generic braiding theorem therefore gives its compatibility with Koszul symmetry.
Its auxiliary instances are hidden from the module packaging the tensor constraints.
(blueprint: lem-sf-condensed-derived-pullback-braiding)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical condensed pullback tensor comparison commutes with the localized
Koszul symmetry. Source: the upstream derived pullback braiding argument.
The underived comparison commutes with the braiding. Apply the generic theorem
that left derivation preserves this equation, then identify the generic comparison
with the canonical pullback comparison using their common counit characterization.
Both derived braidings are the specified localized signed Koszul braiding.
(blueprint: lem-sf-condensed-derived-pullback-braiding) -/
theorem condensedPullbackTensorKoszul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (((leftDerivedUpperStarTensorIso Λ f).app K).app N).hom ≫
      (CategoryTheory.derivedTensorKoszulSymmetry _
        (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj N)).hom =
      L((f)^*⟦Λ⟧).map
          (CategoryTheory.derivedTensorKoszulSymmetry _ K N).hom ≫
        (((leftDerivedUpperStarTensorIso Λ f).app N).app K).hom := by
  let := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
  let := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  change
    ((leftDerivedUpperStarTensor Λ f).app K).app N ≫
        (β_ (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj N)).hom =
      L((f)^*⟦Λ⟧).map (β_ K N).hom ≫
        ((leftDerivedUpperStarTensor Λ f).app N).app K
  have h := Functor.leftDerivedFunctor_map_braiding_hom_δ (f)^*⟦Λ⟧
    (fun A B ↦ (δ_upperStar_braiding Λ f A B).symm) K N
  simpa only [Functor.leftDerivedFunctorMonoidal_δ,
    ← leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f] using h.symm

end AlgebraicGeometry.ProEtale.CondensedRing
