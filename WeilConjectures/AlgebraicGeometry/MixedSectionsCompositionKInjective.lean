/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
import WeilConjectures.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.MixedSectionsLeftUnitNormalization
import WeilConjectures.AlgebraicGeometry.MixedSectionsRightUnitNormalization

/-! # Mixed Leray composition on K-injective complexes

## References

* Stacks Project, Tags 08HY, 0D5T and 0D5W.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

-- Checking the canonical comparisons expands sheaf and derived-functor instances.
/-- Composition coherence computed on a K-injective complex (Stacks, Tags 0D5T and 0D5W). -/
theorem mixedSections_composition_coherence_on_kInjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    let F := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)
    let e : schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f ≫ g) :=
      schemeNormalizedDirectImageCompIso f g
    (mixedGlobalSectionsDirectImageIso g).hom.app ((schemeDerivedDirectImage f).obj F) ≫
        (schemeGlobalScalarRestriction g).map
          ((mixedGlobalSectionsDirectImageIso f).hom.app F) =
      (schemeDerivedGlobalSections Z).map (e.hom.app F) ≫
        (mixedGlobalSectionsDirectImageIso (f ≫ g)).hom.app F ≫
        (schemeGlobalScalarRestrictionCompIso f g).hom.app
          ((schemeDerivedGlobalSections X).obj F) := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let Dfg := RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom
  let HZ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  let e := schemeNormalizedDirectImageCompIso f g
  let a := HZ.rightDerivedFunctorUnit.app ((Dfg.mapHomotopyCategory (.up ℤ)).obj K)
  let t := Dfg.rightDerivedFunctorUnit.app K
  have : IsIso a := isIso_directImage_globalSections_unit_on_kInjective (f ≫ g) I
  have : IsIso t := inferInstance
  let p := a ≫ (schemeDerivedGlobalSections Z).map t ≫
    (schemeDerivedGlobalSections Z).map (e.inv.app (DerivedCategory.Qh.obj K))
  have : IsIso p := by dsimp [p]; infer_instance
  apply (cancel_epi p).1
  exact (mixedSections_left_unit_normalization f g I).trans
    (mixedSections_right_unit_normalization f g I).symm

end AlgebraicGeometry
