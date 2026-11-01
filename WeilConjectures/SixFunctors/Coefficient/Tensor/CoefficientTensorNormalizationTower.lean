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

private theorem exactRestrictionComposition_eq (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) :
    Functor.exactDerivedRestrictionComposition
      (normalizedDVRModuleRes l E X h) (scalarReductionRestriction l E X n)
      (scalarReductionRestriction l E X m) (resComp l E X D hl h) =
        normalizedDVRResCompletedComp l E X D hl h := by
  rfl

end CoefficientTensorTowerProof

-- Preserve the original statement's unused intermediate closed structure `SB`.
set_option linter.unusedVariables false in
end WeilConjectures
