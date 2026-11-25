/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Underived models for the open counit computation

## References

* Stacks Project, Tags 08FE and 08BV
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

/-- The sectionwise open-composition identification, before derivation (Stacks, Tag 08FE). -/
def schemeMVUnderivedOpenComposition {X Y : Scheme.{u}} (h : X ⟶ Y) (U : Y.Opens) :
    RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage h.toLRSHom.toShHom ≅
      RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom :=
  Scheme.Modules.pushforwardComp (h ⁻¹ᵁ U).ι h ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι h U).symm ≪≫
    (Scheme.Modules.pushforwardComp (h ∣_ U) U.ι).symm

/-- The sectionwise open-restriction identification used by the canonical comparison
(Stacks, Tag 08FE). -/
def schemeMVUnderivedOpenRestriction {X Y : Scheme.{u}} (h : X ⟶ Y) (U : Y.Opens) :
    RingedSpace.moduleDirectImage h.toLRSHom.toShHom ⋙ schemeOpenRestriction Y U ≅
      schemeOpenRestriction X (h ⁻¹ᵁ U) ⋙
        RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom := by
  refine Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv U) ≪≫
    ?_ ≪≫ Functor.isoWhiskerRight
      (Scheme.Modules.overFunctorEquiv (h ⁻¹ᵁ U)).symm _
  change Scheme.Modules.pushforward h ⋙ Scheme.Modules.restrictFunctor U.ι ≅
    Scheme.Modules.restrictFunctor (h ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (h ∣_ U)
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · refine NatIso.ofComponents (fun W ↦ eqToIso ?_) ?_
    · exact image_morphismRestrict_preimage h U W
    · cat_disch
  · ext W x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    dsimp
    exact congr($(morphismRestrict_app h U W.unop) x).symm

/-- The open-composition model on homotopy categories, with explicit composition factors
(Stacks, Tag 08FE). -/
def schemeMVHomotopyOpenComposition {X Y : Scheme.{u}} (h : X ⟶ Y) (U : Y.Opens) :
    (RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (schemeMVUnderivedOpenComposition h U)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom)) (ComplexShape.up ℤ)).symm

/-- The open-restriction model on homotopy categories, with explicit composition factors
(Stacks, Tag 08FE). -/
def schemeMVHomotopyOpenRestriction {X Y : Scheme.{u}} (h : X ⟶ Y) (U : Y.Opens) :
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (schemeOpenRestriction Y U).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (schemeOpenRestriction X (h ⁻¹ᵁ U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (schemeMVUnderivedOpenRestriction h U)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (schemeOpenRestriction X (h ⁻¹ᵁ U) ⋙
        RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom)) (ComplexShape.up ℤ)).symm

/-- The open adjunction on homotopy categories, with the right functor specialized once
(Stacks, Tag 08BV). -/
def schemeMVHomotopyOpenAdjunction (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      (RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  let a : schemeOpenRestriction X U ⊣
    RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom := schemeOpenModuleAdjunction X U
  a.mapHomotopyCategory (ComplexShape.up ℤ)

end AlgebraicGeometry
