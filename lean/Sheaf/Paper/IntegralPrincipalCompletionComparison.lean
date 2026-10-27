/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
import all Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion

/-! # Unit-preserving comparison of principal and integral completion

Source: Bhatt--Scholze, Proposition 3.5.1; Stacks Tags 093M, 099B and 0941.
(blueprint: lem-pur-integral-principal-completion-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsCommHasDerivedCategory integralOperationsSiteSmall
  integralOperationsAbLocallyBijective integralOperationsAbSheafify
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] HasDerivedCategory.standard
  IntegralOnSlice.completion IntegralOnSlice.completionUnit
  IntegralOnSlice.completionComparison
  CategoryTheory.PrincipalQuotientCompletion.quotientRoos
open Opposite
open scoped ChangeOfRings


private local instance comparisonSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _

private local instance comparisonAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance comparisonAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

private theorem unit_comparison
    {C : Type*} [Category C] {Q A B Z : C}
    (u : Q ⟶ A) (v : Q ⟶ B) (a : A ≅ Z) (b : B ≅ Z)
    (h : u ≫ a.hom = v ≫ b.hom) :
    u ≫ (a ≪≫ b.symm).hom = v := by
  apply (cancel_mono b.hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using h

private theorem transport_unit_comparison
    {C : Type*} [Category C] (A B : C ⥤ C)
    (u : 𝟭 C ⟶ A) (v : 𝟭 C ⟶ B) {Q R : C}
    (e : Q ≅ R) (d : A.obj Q ≅ B.obj Q)
    (hd : u.app Q ≫ d.hom = v.app Q) :
    u.app R ≫ ((A.mapIso e).symm ≪≫ d ≪≫ B.mapIso e).hom = v.app R := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  have hn := u.naturality e.inv
  have hv := v.naturality e.hom
  simp only [Functor.id_map] at hn hv
  erw [← Category.assoc, ← hn, Category.assoc, reassoc_of% hd,
    ← hv, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- A supplied principal quotient completion agrees with the actual integral completion,
with the specified unit preserved. Source: Bhatt--Scholze, Proposition 3.5.1;
Stacks Tags 093M, 099B and 0941.
(blueprint: lem-pur-integral-principal-completion-comparison).
Proof: choose a good flat K-flat representative. The normalized quotient maps identify
its principal quotient tower with the actual residue tower, including all transitions
and the augmentation. The induced signed Roos comparison preserves both product
coordinates, so it preserves the zero shifted coordinate of the unit. The supplied
model counit is invertible on this representative. Compose it with the localized
Roos comparison and the inverse of the actual completion's representative comparison.
Their unit-computes equations give the required unit equation. Finally transport this
isomorphism along the representative isomorphism by naturality of the two units.
This argument includes the zero complex and empty scheme and requires no completeness
or constructibility of the input. -/
theorem principalIntegralCompletionComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (C : @CategoryTheory.PrincipalQuotientCompletion.Model.{u + 1, u, u + 1, u + 2}
      W.ProEt inferInstance (essentiallySmallSelf.{u} _) (ProEt.topology W) inferInstance
      (integralCoefficientAbSheafify.{u, u} W)
      (integralCoefficientAbLocallyBijective.{u, u} W)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
      (integralTowerHasDerivedCategory.{u, u} l E W)
      (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l E W))
    : letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
      letI : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
        integralCoefficientAbSheafify.{u, u} W
      letI : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
        integralCoefficientAbLocallyBijective.{u, u} W
      ∀ Q : DerivedCategory (integralTowerModules.{u, u} l E W),
    ∃ z : C.completion.obj Q ≅ (IntegralOnSlice.completion.{u, u} l E W none).obj Q,
      C.unit.app Q ≫ z.hom = (IntegralOnSlice.completionUnit.{u, u} l E W none).app Q := by
  intro Q
  classical
  let := integralFiniteBiproducts.{u, u} l E W
  let := integralBinaryBiproducts.{u, u} l E W
  let := integralCountableProducts.{u, u} l E W
  have (H : ℕ → CochainComplex (integralTowerModules.{u, u} l E W) ℤ) : HasProduct H :=
    integralComplexProducts.{u, u} l E W H
  let := IntegralOnSlice.goodLocalization.{u, u} l E W none
  let := Localization.essSurj (IntegralOnSlice.qGood.{u, u} l E W none)
    ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod.{u, u} l E W none) (.up ℤ)).inverseImage
      (IntegralOnSlice.Good.{u, u} l E W none).ι)
  let P := (IntegralOnSlice.qGood.{u, u} l E W none).objPreimage Q
  let e : DerivedCategory.Q.obj P.obj ≅ Q :=
    (IntegralOnSlice.qGood.{u, u} l E W none).objObjPreimageIso Q
  obtain ⟨et, het⟩ := quotient_tower_comparison.{u + 1, u + 1, u}
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l E W) P.obj _
    ((IntegralOnSlice.augmentation.{u, u} l E W none).app P.obj)
    (quotient_level_comparison.{u, u} l E W P.obj)
  obtain ⟨z, hz⟩ := quotient_roos_comparison.{u + 1, u + 1, u + 2, u}
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l E W) C P.obj _ _ et het
    (IntegralOnSlice.roosUnit.{u, u} l E W none P.obj)
    (fun p ↦ roosLift_χ
      (X := koszulTowerComplex.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
        ((IntegralOnSlice.tower.{u, u} l E W none).obj P.obj))
      (IntegralOnSlice.productAugmentation.{u, u} l E W none P.obj)
      (integral_product_zero.{u, u} l E W P.obj) p)
  let := C.computes P.obj P.property.1
  let q := DerivedCategory.Q (C := integralTowerModules.{u, u} l E W)
  let a := asIso (C.counit.app P.obj) ≪≫ q.mapIso z
  let b := (IntegralOnSlice.completionComparison.{u, u} l E W none).app P
  have hc : C.unit.app (q.obj P.obj) ≫ (C.counit.app P.obj ≫ q.map z.hom) =
      q.map (IntegralOnSlice.roosUnit.{u, u} l E W none P.obj) :=
    (Category.assoc (C.unit.app (q.obj P.obj)) (C.counit.app P.obj)
      (q.map z.hom)).symm.trans
      ((congrArg (fun f ↦ f ≫ q.map z.hom) (C.unit_computes P.obj)).trans
        ((q.map_comp (C.augmentation P.obj) z.hom).symm.trans (congrArg q.map hz)))
  have hd := unit_comparison (C.unit.app (q.obj P.obj))
    ((IntegralOnSlice.completionUnit.{u, u} l E W none).app (q.obj P.obj)) a b
    (hc.trans (integral_unit_computes.{u, u} l E W P).symm)
  exact ⟨(C.completion.mapIso e).symm ≪≫ (a ≪≫ b.symm) ≪≫
    (IntegralOnSlice.completion.{u, u} l E W none).mapIso e,
    transport_unit_comparison C.completion (IntegralOnSlice.completion.{u, u} l E W none)
      C.unit (IntegralOnSlice.completionUnit.{u, u} l E W none) e (a ≪≫ b.symm) hd⟩

end WeilConjectures
