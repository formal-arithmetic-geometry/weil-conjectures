/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement

/-!
# Canonical local scalar adjoints at every finite coefficient stage

Source: archived ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(blueprint: def-weil-pbc-condensed-local-coefficient-adjoints).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonObj MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false

section ScalarUnits
open MonoidalCategory
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  {R S A : C} [MonObj R] [MonObj S] [MonObj A]
  [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ A) [IsMonHom ψ]

omit [IsCommMonObj S] in
private lemma scalar_comp_unit (P : Mod C R) :
    (Mod.extendUnit φ P).hom ≫
      (Mod.extendUnit ψ ((Mod.extendScalars φ).obj P)).hom ≫
        (((Mod.extendScalarsComp φ ψ).inv.app P).hom) =
      (Mod.extendUnit (φ ≫ ψ) P).hom := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Mod.extendRestrictAdjunction (φ ≫ ψ))
    (((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ)).ofNatIsoRight
      (Mod.comapComp φ ψ).symm) P
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, scalar_unit] at h
  have h' := congrArg (fun k ↦ k.hom) h
  change (Mod.extendUnit (φ ≫ ψ) P).hom ≫
      ((Mod.extendScalarsComp φ ψ).hom.app P).hom =
    ((Mod.extendUnit φ P).hom ≫
      (Mod.extendUnit ψ ((Mod.extendScalars φ).obj P)).hom) ≫ 𝟙 _ at h'
  rw [Category.comp_id] at h'
  rw [← Category.assoc]
  apply Eq.trans (congrArg (· ≫ ((Mod.extendScalarsComp φ ψ).inv.app P).hom) h'.symm)
  have hi := congrArg (fun k ↦ k.hom) ((Mod.extendScalarsComp φ ψ).hom_inv_id_app P)
  change ((Mod.extendScalarsComp φ ψ).hom.app P).hom ≫
      ((Mod.extendScalarsComp φ ψ).inv.app P).hom = 𝟙 _ at hi
  rw [Category.assoc, hi]
  exact Category.comp_id _

omit [IsCommMonObj S] in
omit [IsCommMonObj S] in
end ScalarUnits

set_option backward.isDefEq.respectTransparency false

section LocalAdjoints

variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
  (Y : Scheme.{u}) (g : Y ⟶ X)
  (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    ((upperStar Ab.{u + 1} g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))

variable
  (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
  (a : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj P ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
  (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)

set_option backward.isDefEq.respectTransparency false in
end LocalAdjoints
end AlgebraicGeometry.ProEtale
