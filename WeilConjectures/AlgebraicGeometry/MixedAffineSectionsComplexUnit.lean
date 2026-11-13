/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso
import WeilConjectures.AlgebraicGeometry.AffineSectionsUnitTransport

/-! # Sections comparison on ordinary affine chart complexes

## References

* Stacks Project, Tag 06Z0.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The ordinary-to-derived sections comparison, with complex localization endpoints
(Stacks, Tag 06Z0). -/
noncomputable def mixedSectionsComplexUnit (S : Scheme.{u})
    (C : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj
        (((RingedSpace.globalSectionsFunctor S.toRingedSpace).mapHomologicalComplex
          (.up ℤ)).obj C) ⟶
      (schemeDerivedGlobalSections S).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((RingedSpace.globalSectionsFunctor S.toRingedSpace).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app C) ≫
    (RingedSpace.globalSectionsFunctor S.toRingedSpace).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
    (schemeDerivedGlobalSections S).map
      ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- Affine chart complexes are acyclic for the unbounded sections comparison: the comparison
`mixedSectionsComplexUnit` is invertible on termwise-tilde complexes (Stacks, Tag 06Z0). -/
theorem mixedAffineChart_sectionsComplexUnit_isIso (S : Scheme.{u}) [IsAffine S]
    [((tilde.functor Γ(S, ⊤)) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ).Additive]
    (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ) :
    IsIso (mixedSectionsComplexUnit S
      ((((tilde.functor Γ(S, ⊤)) ⋙
        Scheme.Modules.restrictFunctor S.toSpecΓ).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let T := tilde.functor Γ(S, ⊤)
  let E := Scheme.Modules.restrictFunctor S.toSpecΓ
  let : E.Additive := Functor.additive_of_iso
    (Scheme.Modules.restrictFunctorIsoPullback S.toSpecΓ).symm
  let : T.Additive := by dsimp [T]; infer_instance
  let G := RingedSpace.globalSectionsFunctor (Spec Γ(S, ⊤)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom
  have hspec : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((T.mapHomologicalComplex (.up ℤ)).obj P))) := by
    exact (NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorUnit
      ((T.mapHomotopyCategoryFactors (.up ℤ)).app P).symm).mpr
        (affineTildeDerivedSectionsUnit_isIso Γ(S, ⊤)
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  have hchart := affineSectionsUnit_transport S
    ((T.mapHomologicalComplex (.up ℤ)).obj P) hspec
  have hcomp := (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ E)) (.up ℤ)).app P
  have hunit : IsIso
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((T ⋙ E).mapHomologicalComplex (.up ℤ)).obj P))) := by
    exact (NatTrans.isIso_app_iff_of_iso _
      ((HomotopyCategory.quotient _ (.up ℤ)).mapIso hcomp.symm)).mpr hchart
  dsimp [mixedSectionsComplexUnit]
  infer_instance

end AlgebraicGeometry
