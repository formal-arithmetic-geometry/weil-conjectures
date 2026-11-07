/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.CompIsoTransfer
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjColimit
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjCounit

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The adjoint transfer of the derived extensions of scalars on complexes

Let `E, F ≤ k` be finite subextensions of `ℚ̄_ℓ`. Along the adjunctions
`T^X_{E,k} ⊣ D(Res_{E→k})`, `T^X_{E,Ω} ⊣ D(Res_{E→Ω})` and the transitivity isomorphisms
`T^X_{E,k} ⋙ T^X_{k,Ω} ≅ T^X_{E,Ω}`, `T^X_{F,k} ⋙ T^X_{k,Ω} ≅ T^X_{F,Ω}`, a morphism
`T^X_{E,Ω} K ⟶ T^X_{F,Ω} L` is of the form `τ⁻¹ ≫ T^X_{k,Ω} g ≫ τ` as soon as its adjoint
`K ⟶ D(Res_{E→Ω}) T^X_{F,Ω} L` factors through the adjoint transfer
`D(Res_{E→k}) T^X_{F,k} L ⟶ D(Res_{E→Ω}) T^X_{F,Ω} L`
(`CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`).

On the image `L = Q Y` of a complex, this transfer is, modulo the counits of the derived
extensions of scalars and the factorizations of `D(Res)`, the image of the inclusion
`Res_{E→k}(k_X ⊗_{F_X} Y) ⟶ Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` of the colimit cocone
`ProEtale.subfieldExtendScalarsCocone`
(`ProEtale.compIsoTransfer_derivedExtendScalars_Qh`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {E F G : FiniteIntermediateField ℓ}
  (hE : E ≤ G) (hF : F ≤ G)
  (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)

/-- The adjoint transfer of the extensions of scalars on the homotopy categories, on the image of
`Y`, is the image of the inclusion of the colimit cocone `subfieldExtendScalarsCocone`. -/
lemma compIsoTransfer_mapHomotopyCategory_subfieldExtendScalars (k : PadicSubfieldAbove ℓ G) :
    Adjunction.compIsoTransfer
      ((Mod.extendRestrictAdjunction
        (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapHomotopyCategory
        (ComplexShape.up ℤ))
      ((Mod.extendRestrictAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _)) _)
      (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _)) _)
      ((HomotopyCategory.quotient _ _).obj Y) =
    (HomotopyCategory.quotient _ _).map ((subfieldExtendScalarsCocone X ℓ hE hF Y).ι.app k) :=
  Adjunction.compIsoTransfer_mapHomotopyCategory_quotient _ _ _ _ _ Y _ fun _ ↦ rfl

set_option maxHeartbeats 1600000 in
-- Unifying the generic `compIsoTransfer_comparison` with the derived categories of module objects
-- (and their many instances) is slow.
/-- The adjoint transfer `D(Res_{E→k}) T^X_{F,k} (Q Y) ⟶ D(Res_{E→Ω}) T^X_{F,Ω} (Q Y)` is, modulo
the counits and the factorizations of `D(Res)`, the image of the inclusion
`Res_{E→k}(k_X ⊗_{F_X} Y) ⟶ Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` of the colimit cocone. -/
theorem compIsoTransfer_derivedExtendScalars_Qh (k : PadicSubfieldAbove ℓ G) :
    (Mod.comap (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapDerivedCategory.map
        ((Mod.extendScalars
          (padicSubfieldRingObjMap X ℓ (hF.trans k.property))).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj Y)) ≫
      (Mod.comap
        (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((subfieldExtendScalarsCocone X ℓ hE hF Y).ι.app k)) =
    Adjunction.compIsoTransfer
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (padicSubfieldRingObjMap X ℓ (hE.trans k.property)))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E))
        (derivedExtendScalarsCompIso X ℓ (hE.trans k.property))
        (derivedExtendScalarsCompIso X ℓ (hF.trans k.property))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y)) ≫
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory.map
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctorCounit.app
          _) ≫
      (Mod.comap
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactorsh.hom.app _ := by
  have hc := Adjunction.compIsoTransfer_comparison
    ((Mod.extendRestrictAdjunction
        (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapHomotopyCategory
      (ComplexShape.up ℤ))
    ((Mod.extendRestrictAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomotopyCategory
      (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryCompIso
      (Mod.extendScalarsCompIsoOfEq
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hE.trans k.property))) _)
    (Functor.mapHomotopyCategoryCompIso
      (Mod.extendScalarsCompIsoOfEq
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hF.trans k.property))) _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicSubfieldRingObjMap X ℓ (hE.trans k.property)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E))
    (derivedExtendScalarsCompIso X ℓ (hE.trans k.property))
    (derivedExtendScalarsCompIso X ℓ (hF.trans k.property))
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).leftDerivedFunctorCounit
    (asIso (Mod.extendScalars
      (padicSubfieldRingObjMap X ℓ (hF.trans k.property))).leftDerivedFunctorCounit)
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ k.obj)).leftDerivedFunctorCounit
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorCounit
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctorCounit
    (Mod.comap (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapDerivedCategoryFactorsh
    (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactorsh
    (Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh _)
    (derivedExtendScalarsCompIso_hom_app_Qh X ℓ (hE.trans k.property))
    (derivedExtendScalarsCompIso_hom_app_Qh X ℓ (hF.trans k.property))
    ((HomotopyCategory.quotient _ _).obj Y)
  rw [compIsoTransfer_mapHomotopyCategory_subfieldExtendScalars] at hc
  exact hc

end AlgebraicGeometry.ProEtale
