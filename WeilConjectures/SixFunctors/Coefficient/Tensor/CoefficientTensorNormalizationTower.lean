/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorChainSquare
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomTensorAssociatorModel
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

attribute [local instance 2000] finiteHomTensorSiteSmall HasDerivedCategory.standard

namespace CoefficientTensorTowerProof
open CategoryTheory.Functor
attribute [local irreducible] constantSheaf CoefficientClosedStructure.tensor
  SheafOfModules.monoidalCategory coefficientTotalTensor coefficientTensorGenerator
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
  coefficientFiniteQuotientExistence coefficientFiniteQuotientDerivedExistence
  coefficientFiniteQuotientExtension coefficientFiniteQuotientDerived
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.standard SheafOfModules.instPreadditive
  finiteHomTensorRepresentativeComparison coefficientLocalizedCounitModel
  finiteHomTensorComplexAssociator
attribute [local instance] scalarReductionExtensionAdditive

private abbrev calculus := (coefficientDerivedSystemEvaluationCalculus.{u, u} l E X).choose
private abbrev cx (n : ℕ) :=
  (scalarReductionExtension.{u, u} l E X n).mapHomologicalComplex (.up ℤ)
private abbrev comparison (n : ℕ) :=
  finiteHomTensorRepresentativeComparison (scalarReductionExtension.{u, u} l E X n)
    (coefficientFiniteDerivedExtension.{u, u} l E X n) (scalarReductionCounit l E X n)

private theorem comparison_model (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    (comparison l E X n).app P = (coefficientFiniteReductionModel l E X P hp n).hom := by
  exact representativeComparison_model _ _ _ P
    (coefficientFiniteReductionCounit_isIso l E X P hp n)

private theorem comparison_unit (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (coefficientFiniteAdjunction l E X n).unit.app (DerivedCategory.Q.obj P) ≫
        (coefficientFiniteDerivedRestriction l E X n).map ((comparison l E X n).app P) ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
          ((cx l E X n).obj P) =
      DerivedCategory.Q.map
        (((coefficientOrdinaryScalarAdjunction l E X n).mapHomologicalComplex (.up ℤ)).unit.app P)
        := by
  let s := coefficientActualScalarDerivedPair l E X n
  let F := cx l E X n
  let a := (coefficientOrdinaryScalarAdjunction l E X n).mapHomologicalComplex (.up ℤ)
  apply normalized_unit_extension DerivedCategory.Q DerivedCategory.Q F
    ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ))
    (coefficientFiniteDerivedExtension l E X n) (coefficientFiniteDerivedRestriction l E X n)
    a (coefficientFiniteAdjunction l E X n) (comparison l E X n)
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P ∧
      ∀ i, SheafOfModules.IsFlatOnSite
        (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) (P.X i))
  · intro Y
    obtain ⟨Y', f, hy, hflat, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Y
    have hsite : ∀ i, SheafOfModules.IsFlatOnSite
        (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
        (Y'.X i) := fun i ↦
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (Y'.X i)).symm (hflat i)
    exact ⟨Y', f, ⟨hy, hsite⟩, q_iso_of_quasi f hq⟩
  · intro Y hy
    have hi : SheafOfModules.scalarChainTranspose
        (completedIntegralCommRingProjectionUnrestricted l E X n) s.extension
        s.extension_additive s.ordinaryAdjunction Y _ (a.unit.app Y) = 𝟙 _ := by
      dsimp only [SheafOfModules.scalarChainTranspose]
      exact a.homEquiv_symm_unit Y
    have hn := s.normalization Y hy.1 hy.2 _ (a.unit.app Y)
    erw [hi, DerivedCategory.Q.map_id, Category.comp_id] at hn
    have hh := congrArg (s.adjunction.homEquiv _ _) hn
    simp only [Equiv.apply_symm_apply] at hh
    erw [s.adjunction.homEquiv_unit] at hh
    have hc : (comparison l E X n).app Y =
        SheafOfModules.scalarPairComplexComparison s.extension s.extension_additive
          s.derived s.counit Y := by
      unfold comparison finiteHomTensorRepresentativeComparison
      dsimp only [SheafOfModules.scalarPairComplexComparison]
      change _ ≫ _ ≫ DerivedCategory.Qh.map
        (𝟙 ((HomotopyCategory.quotient (scalarReductionTarget l E X n) (.up ℤ)).obj
          ((cx l E X n).obj Y))) ≫ _ = _
      erw [DerivedCategory.Qh.map_id, Category.id_comp]
      rfl
    rw [hc]
    change s.adjunction.unit.app (DerivedCategory.Q.obj Y) ≫
        (SheafOfModules.scalarDerivedRestriction
          (completedIntegralCommRingProjectionUnrestricted l E X n)).map
          (SheafOfModules.scalarPairComplexComparison s.extension s.extension_additive
            s.derived s.counit Y) ≫
        (SheafOfModules.scalarRestrictionComparison
          (completedIntegralCommRingProjectionUnrestricted l E X n)).hom.app _ = _
    erw [← Category.assoc, ← hh, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl

private theorem comparison_transpose (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (H : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (t : (cx l E X n).obj P ⟶ H) :
    (coefficientFiniteAdjunction l E X n).homEquiv _ _
        ((comparison l E X n).app P ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map
        (((coefficientOrdinaryScalarAdjunction l E X n).mapHomologicalComplex
          (.up ℤ)).homEquiv _ _ t) ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app H := by
  let d := coefficientFiniteAdjunction l E X n
  let a := (coefficientOrdinaryScalarAdjunction l E X n).mapHomologicalComplex (.up ℤ)
  have hu : d.homEquiv _ _ ((comparison l E X n).app P) =
      DerivedCategory.Q.map (a.unit.app P) ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
          ((cx l E X n).obj P) := by
    rw [d.homEquiv_unit]
    apply (Iso.eq_comp_inv ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.app
      ((cx l E X n).obj P))).2
    erw [Category.assoc]
    exact comparison_unit l E X n P
  rw [d.homEquiv_naturality_right, hu]
  have hn := (NatTrans.naturality
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv t).symm
  change (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app _ ≫
      (coefficientFiniteDerivedRestriction l E X n).map (DerivedCategory.Q.map t) =
    DerivedCategory.Q.map (((scalarReductionRestriction l E X n).mapHomologicalComplex
      (.up ℤ)).map t) ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app H at hn
  erw [Category.assoc, hn, ← Category.assoc, ← DerivedCategory.Q.map_comp]
  rfl

private def resComp (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) :
    normalizedDVRModuleRes l E X h ⋙ scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E X m :=
  normalizedDVRRestrictionCompIso (completedIntegralCoefficientProjection l E X D hl n)
      (normalizedDVRQuotient l E X h) ≪≫
    eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f)
      (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op))

private def chainAssoc (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) :
    cx l E X n ⋙ finiteHomTensorExtensionComplex l E X h ≅ cx l E X m :=
  finiteHomTensorComplexAssociator (coefficientOrdinaryScalarAdjunction l E X n)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction h)
    (coefficientOrdinaryScalarAdjunction l E X m) (resComp l E X D hl h)

private abbrev derivedAssoc (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) :=
  Adjunction.leftAdjointCompIso (coefficientFiniteAdjunction l E X n)
    ((calculus l E X).quotientCalculus.adjunction h)
    (coefficientFiniteAdjunction l E X m) (normalizedDVRResCompletedComp l E X D hl h)

private theorem exactRestrictionComposition_eq (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) :
    Functor.exactDerivedRestrictionComposition
      (normalizedDVRModuleRes l E X h) (scalarReductionRestriction l E X n)
      (scalarReductionRestriction l E X m) (resComp l E X D hl h) =
        normalizedDVRResCompletedComp l E X D hl h := by
  rfl

private theorem associatorModel (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (derivedAssoc l E X D hl h).hom.app (DerivedCategory.Q.obj P) ≫
        (comparison l E X m).app P =
      (coefficientFiniteQuotientDerived l E X h).map ((comparison l E X n).app P) ≫
        (finiteHomTensorComparison l E X h).app ((cx l E X n).obj P) ≫
          DerivedCategory.Q.map ((chainAssoc l E X D hl h).hom.app P) := by
  let a := (coefficientOrdinaryScalarAdjunction l E X n).mapHomologicalComplex (.up ℤ)
  let b := ((calculus l E X).quotientCalculus.ordinaryAdjunction h).mapHomologicalComplex
    (.up ℤ)
  let c := (coefficientOrdinaryScalarAdjunction l E X m).mapHomologicalComplex (.up ℤ)
  let ad := coefficientFiniteAdjunction l E X n
  let bd := (calculus l E X).quotientCalculus.adjunction h
  let cd := coefficientFiniteAdjunction l E X m
  let H := (cx l E X m).obj P
  have hu : cd.homEquiv _ _ ((comparison l E X m).app P) =
      DerivedCategory.Q.map (c.unit.app P) ≫
        (scalarReductionRestriction l E X m).mapDerivedCategoryFactors.inv.app H := by
    rw [cd.homEquiv_unit]
    apply (Iso.eq_comp_inv
      ((scalarReductionRestriction l E X m).mapDerivedCategoryFactors.app H)).2
    erw [Category.assoc]
    exact comparison_unit l E X m P
  have hf := Functor.exactDerivedRestrictionComposition_inv_factors
    (normalizedDVRModuleRes l E X h) (scalarReductionRestriction l E X n)
    (scalarReductionRestriction l E X m) (resComp l E X D hl h) H
  rw [exactRestrictionComposition_eq l E X D hl h] at hf
  exact normalized_tensor_comparison_assoc a b c ad bd cd
    (comparison l E X n) (finiteHomTensorComparison l E X h) (comparison l E X m)
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv
    (normalizedDVRModuleRes l E X h).mapDerivedCategoryFactors.inv
    (scalarReductionRestriction l E X m).mapDerivedCategoryFactors.inv
    (comparison_transpose l E X n)
    (WeilConjectures.comparison_transpose l E X h)
    (NatIso.mapHomologicalComplex (resComp l E X D hl h) (.up ℤ))
    (normalizedDVRResCompletedComp l E X D hl h) (chainAssoc l E X D hl h).hom P hu
    (complexAssoc_transpose _ _ _ _ P) hf

private theorem scalar_generators (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ) :
    CoefficientScalarTensorGenerators.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (integralCoefficientCommRingSheaf l E X n) (scalarReductionExtension l E X n)
      (hF := coefficientFiniteExtensionAdditive l E X n)
      (fun M V x ↦ ((coefficientOrdinaryScalarAdjunction l E X n).unit.app M).val.app V x)
      P Q (coefficientScalarTensorIso l E X n P Q) := by
  exact (coefficientScalarTensorIso_exists l E X n P Q).choose_spec.1

private theorem chain_tensor_square (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q) :
    (finiteHomTensorExtensionComplex l E X h).map
        (coefficientScalarTensorIso l E X n P Q).hom ≫
      (tensorChain l E X h _ _
        ((coefficientTensorModelPreservation l E X).1 P hp n)
        ((coefficientTensorModelPreservation l E X).1 Q hq n)).hom ≫
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).map
          (Prod.mkHom ((chainAssoc l E X D hl h).hom.app P)
            ((chainAssoc l E X D hl h).hom.app Q)) =
      (chainAssoc l E X D hl h).hom.app
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)) ≫
        (coefficientScalarTensorIso l E X m P Q).hom := by
  apply finiteHomTensor_chainSquare.{u, u + 1, u}
    (hFadd := coefficientFiniteExtensionAdditive l E X n)
    (hGadd := coefficientFiniteQuotientExtensionAdditive l E X h)
    (hHadd := coefficientFiniteExtensionAdditive l E X m)
    (A := completedIntegralCommRingSheafUnrestricted l E X)
    (B := integralCoefficientCommRingSheaf l E X n)
    (T := integralCoefficientCommRingSheaf l E X m)
    (completedIntegralCoefficientProjection l E X D hl n) (normalizedDVRQuotient l E X h)
    (completedIntegralCoefficientProjection l E X D hl m)
    (coefficientOrdinaryScalarAdjunction l E X n)
    ((calculus l E X).quotientCalculus.ordinaryAdjunction h)
    (coefficientOrdinaryScalarAdjunction l E X m) (chainAssoc l E X D hl h).hom
    (@complexAssoc_unit_section X.ProEt _ (ProEt.topology X) _ _ _ _ _
      (completedIntegralCoefficientProjection l E X D hl n) (normalizedDVRQuotient l E X h)
      (completedIntegralCoefficientProjection l E X D hl m)
      (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op)
      (scalarReductionExtension.{u, u} l E X n)
      (coefficientFiniteQuotientExtension.{u, u} l E X h)
      (scalarReductionExtension.{u, u} l E X m)
      (coefficientFiniteExtensionAdditive l E X n)
      (coefficientFiniteQuotientExtensionAdditive l E X h)
      (coefficientFiniteExtensionAdditive l E X m)
      (coefficientOrdinaryScalarAdjunction l E X n)
      ((calculus l E X).quotientCalculus.ordinaryAdjunction h)
      (coefficientOrdinaryScalarAdjunction l E X m))
    P Q (coefficientScalarTensorIso l E X n P Q)
    (tensorChain l E X h _ _
      ((coefficientTensorModelPreservation l E X).1 P hp n)
      ((coefficientTensorModelPreservation l E X).1 Q hq n))
    (coefficientScalarTensorIso l E X m P Q)
  · exact scalar_generators l E X n P Q
  · exact tensorChain_generators l E X h _ _ _ _
  · exact scalar_generators l E X m P Q

private theorem scalar_model (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q) :
    (coefficientFiniteDerivedExtension l E X n).map
        (coefficientIntegralTensorModelIso l E X
          (calculus l E X).toCoefficientDerivedSystemTensors P Q hp hq).hom ≫
      ((calculus l E X).finiteTensor n).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      ((calculus l E X).finiteClosed n).tensor.map
        (Prod.mkHom ((comparison l E X n).app P) ((comparison l E X n).app Q)) =
      (comparison l E X n).app _ ≫
        DerivedCategory.Q.map (coefficientScalarTensorIso l E X n P Q).hom ≫
        (coefficientFiniteTensorModelIso l E X
          (calculus l E X).toCoefficientDerivedSystemTensors n _ _
          ((coefficientTensorModelPreservation l E X).1 P hp n)
          ((coefficientTensorModelPreservation l E X).1 Q hq n)).hom := by
  rw [comparison_model l E X n P hp, comparison_model l E X n Q hq,
    comparison_model l E X n _
      (coefficientTotalTensor_isKFlat.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) P Q hp hq)]
  exact (calculus l E X).finiteTensor_normalization n P Q hp hq

private theorem representative_square (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q) :
    (coefficientFiniteQuotientDerived l E X h).map
        (((calculus l E X).finiteTensor n).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      ((calculus l E X).quotientCalculus.tensor h).hom.app
        ((coefficientFiniteDerivedExtension l E X n).obj (DerivedCategory.Q.obj P),
          (coefficientFiniteDerivedExtension l E X n).obj (DerivedCategory.Q.obj Q)) ≫
      ((calculus l E X).finiteClosed m).tensor.map
        (Prod.mkHom ((derivedAssoc l E X D hl h).hom.app (DerivedCategory.Q.obj P))
          ((derivedAssoc l E X D hl h).hom.app (DerivedCategory.Q.obj Q))) =
      (derivedAssoc l E X D hl h).hom.app
        ((calculus l E X).integralClosed.tensor.obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        ((calculus l E X).finiteTensor m).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let Fa := cx l E X n
  let Fb := finiteHomTensorExtensionComplex l E X h
  let Fc := cx l E X m
  let F := coefficientFiniteDerivedExtension l E X n
  let G := coefficientFiniteQuotientDerived l E X h
  let H := coefficientFiniteDerivedExtension l E X m
  let U := ((calculus l E X).finiteClosed n).tensor
  let V := ((calculus l E X).finiteClosed m).tensor
  let cc := derivedAssoc l E X D hl h
  let hPn := (coefficientTensorModelPreservation l E X).1 P hp n
  let hQn := (coefficientTensorModelPreservation l E X).1 Q hq n
  let hPm := (coefficientTensorModelPreservation l E X).1 P hp m
  let hQm := (coefficientTensorModelPreservation l E X).1 Q hq m
  let hPnm := (calculus l E X).quotientCalculus.preservesKFlat h _ hPn
  let hQnm := (calculus l E X).quotientCalculus.preservesKFlat h _ hQn
  let rR := (coefficientIntegralTensorModelIso l E X
    (calculus l E X).toCoefficientDerivedSystemTensors P Q hp hq).hom
  let _ : IsIso (G.map (F.map rR)) := Iso.isIso_hom
    ((F ⋙ G).mapIso (coefficientIntegralTensorModelIso l E X
      (calculus l E X).toCoefficientDerivedSystemTensors P Q hp hq))
  let rS := (coefficientFiniteTensorModelIso l E X
    (calculus l E X).toCoefficientDerivedSystemTensors n (Fa.obj P) (Fa.obj Q) hPn hQn).hom
  let rT := (coefficientFiniteTensorModelIso l E X
    (calculus l E X).toCoefficientDerivedSystemTensors m
    (Fb.obj (Fa.obj P)) (Fb.obj (Fa.obj Q)) hPnm hQnm).hom
  let rC := (coefficientFiniteTensorModelIso l E X
    (calculus l E X).toCoefficientDerivedSystemTensors m (Fc.obj P) (Fc.obj Q) hPm hQm).hom
  let e (Y : CochainComplex (scalarReductionSource l E X) ℤ) :=
    (comparison l E X n).app Y
  let f (Y : CochainComplex (normalizedDVRModules l E X n) ℤ) :=
    (finiteHomTensorComparison l E X h).app Y
  let g (Y : CochainComplex (scalarReductionSource l E X) ℤ) :=
    (comparison l E X m).app Y
  let z (Y : CochainComplex (scalarReductionSource l E X) ℤ) :=
    DerivedCategory.Q.map ((chainAssoc l E X D hl h).hom.app Y)
  have he (Y : CochainComplex (scalarReductionSource l E X) ℤ)
      (hy : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Y) :
      IsIso (g Y) := by
    dsimp only [g]
    rw [comparison_model l E X m Y hy]
    infer_instance
  have := he P hp
  have := he Q hq
  have : IsIso (Prod.mkHom (g P) (g Q)) := by
    change IsIso ((asIso (g P)).prod (asIso (g Q))).hom
    infer_instance
  have ha := scalar_model l E X n P Q hp hq
  have hb := tensorChain_model l E X h (Fa.obj P) (Fa.obj Q) hPn hQn
  have hc := scalar_model l E X m P Q hp hq
  have hs : V.map (Prod.mkHom (cc.hom.app (DerivedCategory.Q.obj P))
        (cc.hom.app (DerivedCategory.Q.obj Q))) ≫ V.map (Prod.mkHom (g P) (g Q)) =
      V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) ≫
        V.map (Prod.mkHom (f (Fa.obj P)) (f (Fa.obj Q))) ≫
          V.map (Prod.mkHom (z P) (z Q)) := by
    rw [← V.map_comp, ← V.map_comp, ← V.map_comp]
    congr 1
    exact Prod.ext (associatorModel l E X D hl h P) (associatorModel l E X D hl h Q)
  have hr : DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m)).map
        (Prod.mkHom ((chainAssoc l E X D hl h).hom.app P)
          ((chainAssoc l E X D hl h).hom.app Q))) ≫ rC =
        rT ≫ V.map (Prod.mkHom (z P) (z Q)) := by
    exact ((calculus l E X).finiteTensorModel m).comparison.hom.naturality
      (Prod.mkHom (ObjectProperty.homMk
        (X := ⟨Fb.obj (Fa.obj P), hPnm⟩) (Y := ⟨Fc.obj P, hPm⟩)
        ((chainAssoc l E X D hl h).hom.app P))
      (ObjectProperty.homMk
        (X := ⟨Fb.obj (Fa.obj Q), hQnm⟩) (Y := ⟨Fc.obj Q, hQm⟩)
        ((chainAssoc l E X D hl h).hom.app Q)))
  have hnat := ((calculus l E X).quotientCalculus.tensor h).hom.naturality
    (Prod.mkHom (e P) (e Q))
  change G.map (U.map (Prod.mkHom (e P) (e Q))) ≫ _ =
    _ ≫ V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) at hnat
  have hf := (finiteHomTensorComparison l E X h).naturality
    (coefficientScalarTensorIso l E X n P Q).hom
  have hga := map_three_eq_three G ha
  have ht := map_three_comp_eq DerivedCategory.Q (chain_tensor_square l E X D hl h P Q hp hq)
  have hcc := associatorModel l E X D hl h
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q))
  have hn := cc.hom.naturality rR
  apply (cancel_epi (G.map (F.map rR))).mp
  apply (cancel_mono (V.map (Prod.mkHom (g P) (g Q)))).mp
  simp only [Category.assoc]
  exact CategoryTheory.ScalarHomTensor.diagram_paste
    hs hnat.symm hga hb hf hr.symm ht hcc.symm hc.symm hn.symm

private theorem integral_representatives (Y : DerivedCategory (scalarReductionSource l E X)) :
    ∃ P : CochainComplex (scalarReductionSource l E X) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ Y) := by
  apply representatives_of_resolution
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P) ?_ Y
  intro P
  obtain ⟨P', p, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P
  exact ⟨P', p, hp, hq⟩

end CoefficientTensorTowerProof

-- Preserve the original statement's unused intermediate closed structure `SB`.
set_option linter.unusedVariables false in
/-- Successive finite coefficient tensor normalization, the second component of the coherence.
Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility, fix-prop-coherence.proof.md.
On K-flat representatives both scalar association paths are the same balanced tensor map.
(blueprint: lem-sf-coefficient-tensor-normalization-tower). -/
theorem coefficientTensor_normalization_tower
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∀ (n m : ℕ) (h : m ≤ n),
      let SA := scalarIntegralClosed l E X
      let SB := finiteIntrinsicClosed l E X n
      let SC := finiteIntrinsicClosed l E X m
      let F := coefficientFiniteDerivedExtension l E X n
      let G := coefficientFiniteQuotientDerived l E X h
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n
      let ν := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h
      let ξ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor m
      let α := Adjunction.leftAdjointCompIso (coefficientFiniteAdjunction l E X n)
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
        (coefficientFiniteAdjunction l E X m) (normalizedDVRResCompletedComp l E X D hl h)
      ∀ K M : DerivedCategory (scalarReductionSource l E X),
        G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
            SC.tensor.map (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
          α.hom.app (SA.tensor.obj (K, M)) ≫ ξ.hom.app (K, M) := by
  intro n m h SA SB SC F G μ ν ξ α K M
  exact tensor_square_descent
    SA.tensor SB.tensor SC.tensor F G (coefficientFiniteDerivedExtension.{u, u} l E X m)
    μ ν ξ α DerivedCategory.Q.obj
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (CoefficientTensorTowerProof.integral_representatives l E X)
    (CoefficientTensorTowerProof.representative_square l E X D hl h) K M

end WeilConjectures
