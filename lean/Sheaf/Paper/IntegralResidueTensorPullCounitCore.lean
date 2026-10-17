/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorPullPresentation
public import Sheaf.Paper.IntegralResidueScalarCounitModel
import Sheaf.Paper.IntegralReductionTensor
import Sheaf.Paper.IntegralResidueTensorModel
import Sheaf.Paper.IntegralResidueTensorPresentation

/-! The normalized middle composite for the residue tensor-pull counit.

Source: Bhatt--Scholze, Remark 6.8.15 and the proof of Lemma 6.5.9(5), p. 51.
(blueprint: new-integral-residue-tensor-pull-counit-core)
-/

@[expose] public section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
noncomputable section GenericNormalization
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
local instance : BraidedCategory (DerivedCategory C) :=
  DerivedMonoidal.braidedCategory (DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))

private theorem tensorPresentation_fac (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      (Functor.tensorModelCoefficientIso B).hom ▷ DerivedCategory.Qh.obj P ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (Functor.tensorModelCoefficient B) P =
      ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  simp only [derivedTensorPresentationIso, derivedTensorSingleIso, Iso.trans_hom,
    NatTrans.comp_app, BraidedCategory.tensorLeftIsoTensorRight,
    Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.mapIso_hom, Iso.symm_hom, Functor.tensorModelCoefficientIso,
    curriedTensor_map_app]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  change _ ≫ _ ≫ (DerivedCategory.tensorLeftQhObjCounit
    (Functor.tensorModelCoefficient B)).app P = _
  simp only [Functor.leftDerivedNatIso_hom, Functor.leftDerivedNatTrans_app,
    Functor.leftDerivedUnique, Functor.leftDerivedNatTrans_app_assoc,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]

variable {D : Type u₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]

omit [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D] in
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientCounit_fac (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (B : C) (B' : D)
    (e : F.obj B ≅ B') :
    let c := F.singleFunctorCompLeftDerivedFunctorIso.app B ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso e
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj B) ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single D (.up ℤ) 0).mapIso e)
    c.inv ≫ F.leftDerivedFunctor.map (Functor.tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient B) =
      (Functor.tensorModelCoefficientIso B').hom ≫ DerivedCategory.Qh.map eH.inv := by
  dsimp only
  have h := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    (Functor.tensorModelCoefficient B)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← h]
  simp only [Functor.singleFunctorCompLeftDerivedFunctorIso, NatIso.trans_app, Iso.trans_inv,
    Iso.trans_hom, Iso.app_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.mapIso_inv, Functor.tensorModelCoefficientIso,
    Category.assoc]
  erw [F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [Functor.tensorModelCoefficient, Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.app_hom, NatTrans.id_app,
    Iso.symm_hom, Category.id_comp, Functor.map_comp, Category.assoc]
  erw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    F.mapDerivedCategory.map_id, Category.id_comp,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rfl

local instance : BraidedCategory (DerivedCategory D) :=
  DerivedMonoidal.braidedCategory (DerivedCategory.Qh (C := D))
    (HomotopyCategory.quasiIso D (.up ℤ))

set_option backward.isDefEq.respectTransparency false in
private theorem tensorPullCounit_fac (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (B : C) (B' : D)
    (e : F.obj B ≅ B') (H : DerivedCategory D ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso D (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    let c := F.singleFunctorCompLeftDerivedFunctorIso.app B ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso e
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj B) ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single D (.up ℤ) 0).mapIso e)
    (derivedTensorPresentationIso B' H ε ≪≫
        (curriedTensor (DerivedCategory D)).flip.mapIso c.symm).hom.app
          (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P)) ≫
      Functor.tensorModelTarget F B P =
      H.map (F.leftDerivedFunctorCounit.app P) ≫
        ε.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
            eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) := by
  dsimp only
  unfold Functor.tensorModelTarget
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.flip_map_app, curriedTensor_obj_map, Iso.symm_hom, Category.assoc]
  erw [BraidedCategory.braiding_inv_naturality_right_assoc]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc]
  erw [coefficientCounit_fac F B B' e]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← BraidedCategory.braiding_inv_naturality_left_assoc]
  have hn := (derivedTensorPresentationIso B' H ε).hom.naturality
    (F.leftDerivedFunctorCounit.app P)
  dsimp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app] at hn
  erw [← reassoc_of% hn]
  erw [Functor.LaxMonoidal.μ_natural_left]
  simp only [Functor.map_comp]
  erw [reassoc_of% tensorPresentation_fac B' H ε
    ((F.mapHomotopyCategory (.up ℤ)).obj P)]

end GenericNormalization
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency false in
/-- The coefficient-adjusted tensor model composite factors through the inverse of
its X tensor presentation.  This is the middle identity used to normalize the
full tensor-pull counit.  It is strictly weaker than the target identity: the
X presentation map is absent from the left side and its inverse is present on
 the right.

The proof expands the exact-F coefficient comparison and the two defining
left-derived comparison equations.  Naturality of the tensorator and of the
lax map of `DerivedCategory.Qh` moves the coefficient comparison to the first
factor; the defining equation for `derivedTensorPresentationIso` then gives the
presentation counit.  The remaining maps are the displayed homotopy single
comparison and the homotopy image of the ordinary coefficient isomorphism.
This is the explicit formal calculation from Remark 6.8.15, with no flatness
assumption.
(blueprint: new-integral-residue-tensor-pull-counit-core) -/
theorem integralResidue_tensorPullCounit_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    letI := residueOrdinaryUpperStarMonoidal A f
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let φX := coefficientMap (integralReductionMap ℓ E) X
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
      unfold H B' residueExchangeOrdinaryCoefficient
        residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit φX
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    let N :=
      ((curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
        (residueExchangeCoefficientPullIso ℓ E f).symm).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
        residueExchangeTensorModelTarget ℓ E f P
    let R := H.map a ≫
      εX.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
      ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P)
    N = (residueExchangeTensorIso ℓ E X).inv.app
      ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫ R := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing
