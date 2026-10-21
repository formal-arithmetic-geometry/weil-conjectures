/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Canonical global Hom adjunction

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.schemeGlobalHomAdjunctionIso` and its companions. The source module
`WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso` is now in the import closure
of the downstream Sheaf modules, so the former copy at this path would clash with it.
The source renamed the Leray comparison and the pullback tensorator
(`mixedGlobalSectionsDirectImageIso`, `mixedHomTensorPullbackIso`, with independent
module localization universes); the former names at this path are kept below as
their specializations, with their statements unchanged.

Source: Stacks Project, duality.tex, Tag 0B6I (lemma-iso-global-hom).
(blueprint: lem-pc-global-hom-adjunction).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The canonical Leray comparison is the identity on underived sections and is
compatible with the right-derived units: the former name of
`exists_mixedGlobalSectionsDirectImageIso` at this path.
Source: Stacks, Tags 0B6I and 0D5T (blueprint: lem-pc-global-hom-adjunction). -/
theorem exists_schemeGlobalSectionsDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (c₀ : RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace ≅
      RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        ModuleCat.restrictScalars.{u}
          (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
          (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom)
      (c : schemeDerivedDirectImage f ⋙ schemeDerivedGlobalSections Y ≅
        schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f),
      (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (x : (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj F),
        (c₀.hom.app F).hom x = x) ∧
      (∀ K : HomotopyCategory
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (schemeDerivedGlobalSections Y).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
          c.hom.app (DerivedCategory.Qh.obj K) =
        (DerivedCategory.Qh
          (C := ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))).map
          ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
              RingedSpace.globalSectionsFunctor Y.toRingedSpace))
            (ComplexShape.up ℤ)).hom.app K ≫
            (Functor.mapHomotopyCategoryCompIso c₀.symm
              (ComplexShape.up ℤ)).inv.app K) ≫
          (ModuleCat.restrictScalars.{u}
            (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
            (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
            f.appTop.hom).mapDerivedCategoryFactorsh.inv.app
              (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K) ≫
          (schemeGlobalScalarRestriction f).map
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K)) :=
  exists_mixedGlobalSectionsDirectImageIso f

/-- The canonical derived Leray isomorphism, chosen with its unit compatibility.
Source: Stacks, Tags 0B6I and 0D5T (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalSectionsDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeDerivedDirectImage f ⋙ schemeDerivedGlobalSections Y ≅
      schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f :=
  Classical.choose (Classical.choose_spec (exists_schemeGlobalSectionsDirectImageIso f))

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The canonical comparison of def-pc-derived-pullback-tensor-comparison is an iso:
the former name of `exists_mixedHomTensorPullbackIso` at this path.
Source: Stacks, Tags 079U and 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
theorem exists_schemeHomTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X),
      IsCanonicalPullbackTensorComparison f (fun K L ↦ t.hom.app (K, L)) :=
  exists_mixedHomTensorPullbackIso f

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical derived pullback tensor iso, specified on K-flat representatives.
Source: Stacks, Tags 079U and 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeHomTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X) :=
  let t := Classical.choose (exists_schemeHomTensorPullbackIso f)
  NatIso.ofComponents (fun Z ↦ asIso (t.hom.app Z)) (fun a ↦ t.hom.naturality a)

end AlgebraicGeometry
