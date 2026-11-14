/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restricting the unit of any right adjunction of open restriction is invertible.
There are no compactness, quasi-coherence, closed support, or triangle hypotheses
(Stacks, Tags 08BS and 08FE). -/
theorem derived_open_unit_restriction_isIso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (R : DerivedCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (K : schemeDerivedCategory X) :
    IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.map
      (adj.unit.app K)) := by
  classical
  let A := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let G := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  obtain ⟨_, _, hlim, hcolim, ⟨adjG⟩⟩ := open_restriction_adjunction_exact X.toRingedSpace U
  let : PreservesFiniteLimits G := hlim
  let : PreservesFiniteColimits G := hcolim
  let : G.Additive := adjG.left_adjoint_additive
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let adjD : G.mapDerivedCategory ⊣ F.mapDerivedCategory :=
    (adjG.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
      G.mapDerivedCategory F.mapDerivedCategory
  obtain ⟨e⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace U
  let : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits G F
  let : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits G F
  let eD : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
    (Functor.mapDerivedCategoryCompIso G F) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A
  let ff := adjD.fullyFaithfulLOfCompIsoId eD
  let ffR := (Adjunction.Triple.fullyFaithfulEquiv ⟨adjD, adj⟩) ff
  let : R.Full := ffR.full
  let : R.Faithful := ffR.faithful
  exact inferInstance

end AlgebraicGeometry
