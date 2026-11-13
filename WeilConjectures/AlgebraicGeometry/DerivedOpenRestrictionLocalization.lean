/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Derived open restriction is a localization

## References

* Stacks Project, Tags 08FE and 08BS
-/

@[expose] public section

universe u w wO
open CategoryTheory CategoryTheory.Limits
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exact derived restriction localizes at the morphisms it turns into isomorphisms
(Stacks, Tags 08BT, 08BS and 00A7). -/
theorem schemeDerivedOpenRestriction_isLocalization (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    R.IsLocalization
      ((MorphismProperty.isomorphisms (schemeDerivedCategory U.toScheme)).inverseImage R)
      := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let e : B ≌ C := Scheme.Modules.overEquiv U
  let E : B ⥤ A :=
    SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  let R : A ⥤ B := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  obtain ⟨hRlim, hRcolim, hElim, hEcolim, ⟨adj⟩⟩ :=
    open_restriction_adjunction_exact X.toRingedSpace U
  have : PreservesFiniteLimits E := hElim
  have : PreservesFiniteColimits E := hEcolim
  have : PreservesFiniteLimits R := hRlim
  have : PreservesFiniteColimits R := hRcolim
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  let L := e.inverse ⋙ E
  let S := R ⋙ e.functor
  let a : L ⊣ S := e.symm.toAdjunction.comp adj
  have : PreservesFiniteLimits L := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits L := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits S := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits S := comp_preservesFiniteColimits _ _
  have : L.IsLeftAdjoint := a.isLeftAdjoint
  have : S.IsRightAdjoint := a.isRightAdjoint
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  obtain ⟨i⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace U
  let j : L ⋙ S ≅ 𝟭 C :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight i e.functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.leftUnitor _) ≪≫ e.counitIso
  have : CatCommSq (L.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  have : CatCommSq (S.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q S.mapDerivedCategory :=
    ⟨S.mapDerivedCategoryFactors.symm⟩
  let d := (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    L.mapDerivedCategory S.mapDerivedCategory
  let k : L.mapDerivedCategory ⋙ S.mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
    (Functor.mapDerivedCategoryCompIso L S) ≪≫
      Functor.mapDerivedCategoryNatIso j ≪≫ Functor.mapDerivedCategoryIdIso C
  have : L.mapDerivedCategory.Full := (d.fullyFaithfulLOfCompIsoId k).full
  have : L.mapDerivedCategory.Faithful := (d.fullyFaithfulLOfCompIsoId k).faithful
  exact d.isLocalization'


end AlgebraicGeometry
