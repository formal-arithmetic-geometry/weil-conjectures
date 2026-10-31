/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionRes

/-!
# The commutation of `ν^*` with the derived extension of scalars is a mate

Let `φ : Λ →+* Λ'` be a surjective morphism of rings with principal kernel and `Ψ` the derived
extensions of scalars along `φ`, left adjoint to the restrictions of scalars `Res`. This file
shows that the commutation `χ : ν^* Ψ ≅ Ψ ν^*` (`ProEtale.comparisonUpperStarDerivedExtendScalarsIso`)
is the mate under `Ψ ⊣ Res` of the commutation `Res ν^* ≅ ν^* Res`
(`ProEtale.comparisonUpperStarDerivedExtendScalarsIso_hom_eq`). Consequently the base change
map `Rν_* L ⊗ᴸ Λ' ⟶ Rν_*(L ⊗ᴸ Λ')` has a simple transpose under `Ψ ⊣ Res`: it is `Rν_*` of the
unit `L ⟶ Res(L ⊗ᴸ Λ')` followed by the commutation of `Res` with `Rν_*`
(`ProEtale.unit_app_comp_map_derivedExtendScalarsComparisonLowerStarMap_app`).
-/

@[expose] public section


universe u

open CategoryTheory Category Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'} (X : Scheme.{u})

variable [IsNoetherianRing Λ] (hφ : Function.Surjective φ) {a : Λ}
  (ha : RingHom.ker φ = Ideal.span {a})

/-- The unit of `Ψ ⊣ Res` on pro-étale sheaves, on the image of a complex. -/
lemma derivedExtendScalarsAdjunction_unit_app_Qh (K : HomotopyCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)) :
    have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
    (ProEtale.derivedExtendScalarsAdjunction hφ ha X).unit.app (DerivedCategory.Qh.obj K) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map
        ((Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedFunctorCounit.app K) =
    DerivedCategory.Qh.map
        (((Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app K) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactorsh.inv.app
        (((Sheaf.extendScalars (Scheme.ProEt.topology X) φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) :=
  have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
  Adjunction.derivedAdjunction_ofNatIsoRight_unit_app_Qh _ K

/-- The unit of `Ψ ⊣ Res` on étale sheaves, on the image of a complex. -/
lemma _root_.AlgebraicGeometry.Etale.derivedExtendScalarsAdjunction_unit_app_Qh
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)) :
    have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
    (Etale.derivedExtendScalarsAdjunction hφ ha X).unit.app (DerivedCategory.Qh.obj K) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        ((Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedFunctorCounit.app K) =
    DerivedCategory.Qh.map
        (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app K) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactorsh.inv.app
        (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) :=
  have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
  Adjunction.derivedAdjunction_ofNatIsoRight_unit_app_Qh _ K

lemma comparisonUpperStarDerivedExtendScalarsCounit_app
    (Y : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)) :
    have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
    (comparisonUpperStarDerivedExtendScalarsCounit hφ ha X).app Y =
      (ProEtale.derivedExtendScalars hφ ha X).map
          ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.hom.app Y) ≫
        (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedFunctorCounit.app
          (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (comparisonUpperStarCompExtendScalarsIso φ X) (ComplexShape.up ℤ)).hom.app Y) := by
  intro
  simp [comparisonUpperStarDerivedExtendScalarsCounit,
    Functor.mapDerivedCategoryCompLeftDerivedFunctorCounit]
  erw [Category.id_comp]
  rfl

/-- The transpose under `Ψ ⊣ Res` of the counit `comparisonUpperStarDerivedExtendScalarsCounit` on
the image of a complex. -/
lemma homEquiv_comparisonUpperStarDerivedExtendScalarsCounit_app
    (Y : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)) :
    ((ProEtale.derivedExtendScalarsAdjunction hφ ha X).homEquiv _ _)
        ((comparisonUpperStarDerivedExtendScalarsCounit hφ ha X).app Y) =
      (ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.hom.app Y ≫
        DerivedCategory.Qh.map
          (((Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app
              (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y)) ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactorsh.inv.app
          (((Sheaf.extendScalars (Scheme.ProEt.topology X) φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
              (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y)) ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map
          (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (comparisonUpperStarCompExtendScalarsIso φ X) (ComplexShape.up ℤ)).hom.app Y)) := by
  have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
  rw [Adjunction.homEquiv_unit, comparisonUpperStarDerivedExtendScalarsCounit_app,
    Functor.map_comp, Functor.map_comp]
  erw [← (ProEtale.derivedExtendScalarsAdjunction hφ ha X).unit.naturality_assoc]
  dsimp only [Functor.id_map, Functor.comp_obj]
  rw [reassoc_of% (derivedExtendScalarsAdjunction_unit_app_Qh X hφ ha
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y))]

lemma derivedExtendScalarsComparisonUpperStarCounit_app
    (Y : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)) :
    have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
    (derivedExtendScalarsComparisonUpperStarCounit hφ ha X).app Y =
      D(ν^*(X)[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedFunctorCounit.app Y) ≫
        (ν^*(X)[ModuleCat.{u + 1} Λ']).mapDerivedCategoryFactorsh.hom.app
          (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Sheaf.extendScalars X.smallEtaleTopology φ ⋙ ν^*(X)[ModuleCat.{u + 1} Λ']))
          (ComplexShape.up ℤ)).hom.app Y) := by
  intro
  simp [derivedExtendScalarsComparisonUpperStarCounit,
    Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit]
  erw [Category.id_comp]

variable (φ) in
/-- The commutation `Res ν^* ≅ ν^* Res` on derived categories, on the image of a complex, modulo
the factorizations of the functors induced by `ν^*` and `Res`. -/
lemma derivedRestrictScalarsCompComparisonUpperStarIso_hom_app_Qh
    (B : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (ComplexShape.up ℤ)) :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactorsh.inv.app B) ≫
      (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom.app (DerivedCategory.Qh.obj B) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map
        ((ν^*(X)[ModuleCat.{u + 1} Λ']).mapDerivedCategoryFactorsh.hom.app B) =
    (ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.hom.app
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj B) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).hom.app B ≫
          (NatTrans.mapHomotopyCategory (restrictScalarsCompComparisonUpperStar φ X)
            (ComplexShape.up ℤ)).app B ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app B) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactorsh.inv.app
        (((ν^*(X)[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (ComplexShape.up ℤ)).obj B) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj
    (asIso (restrictScalarsCompComparisonUpperStar φ X)) B
  rw [asIso_hom] at h
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- The transpose under `Ψ ⊣ Res` of the mate of `derivedRestrictScalarsCompComparisonUpperStarIso`
followed by the counit `derivedExtendScalarsComparisonUpperStarCounit`, on the image of a
complex. -/
lemma homEquiv_mateEquiv_symm_comp_derivedExtendScalarsComparisonUpperStarCounit_app
    (Y : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)) :
    ((ProEtale.derivedExtendScalarsAdjunction hφ ha X).homEquiv _ _)
        (((mateEquiv (Etale.derivedExtendScalarsAdjunction hφ ha X)
          (ProEtale.derivedExtendScalarsAdjunction hφ ha X)).symm
            (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom).natTrans.app
              (DerivedCategory.Qh.obj Y) ≫
          (derivedExtendScalarsComparisonUpperStarCounit hφ ha X).app Y) =
      (ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.hom.app Y ≫
        DerivedCategory.Qh.map
          (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).map
              (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).mapHomotopyCategory
                (ComplexShape.up ℤ)).unit.app Y) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).hom.app
              (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj Y) ≫
            (NatTrans.mapHomotopyCategory (restrictScalarsCompComparisonUpperStar φ X)
              (ComplexShape.up ℤ)).app
              (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj Y) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app
              (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj Y)) ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactorsh.inv.app
          (((ν^*(X)[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj Y)) ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map
          (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (Sheaf.extendScalars X.smallEtaleTopology φ ⋙ ν^*(X)[ModuleCat.{u + 1} Λ']))
            (ComplexShape.up ℤ)).hom.app Y)) := by
  have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
  have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  erw [← unit_mateEquiv_symm (Etale.derivedExtendScalarsAdjunction hφ ha X)
    (ProEtale.derivedExtendScalarsAdjunction hφ ha X)
    (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom (DerivedCategory.Qh.obj Y)]
  rw [derivedExtendScalarsComparisonUpperStarCounit_app, Functor.map_comp, Functor.map_comp,
    Category.assoc]
  erw [← (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom.naturality_assoc
    ((Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedFunctorCounit.app Y)]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, Etale.derivedExtendScalarsAdjunction_unit_app_Qh X hφ ha Y,
    Functor.map_comp_assoc]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (derivedRestrictScalarsCompComparisonUpperStarIso_hom_app_Qh φ X
      (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y))]
  erw [(ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.hom.naturality_assoc]
  rw [Functor.comp_map, ← DerivedCategory.Qh.map_comp_assoc]
  rfl

end AlgebraicGeometry.ProEtale
