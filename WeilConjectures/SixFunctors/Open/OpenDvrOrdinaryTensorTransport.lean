/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import WeilConjectures.SixFunctors.Open.OpenDvrScalarUnitFormula
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
import all WeilConjectures.Algebra.Homology.QuotientIsoTransport.RingIsoQuotientSystemTransport
import all WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Ordinary tensor transport for the DVR coefficient comparison

Source: Stacks Tag 03EK; the ordinary tensor transport step of
`lem-sf-open-dvr-strict-reduction-comparison`.
(blueprint: lem-sf-open-dvr-ordinary-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open MonoidalCategory
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard scalarReductionExistence
  scalarReductionExtension coefficientSequenceRestriction
  coefficientSequenceEvaluation coefficientSequenceTransition coefficientOrdinaryQuotient
  unrestrictedIntegralTransition constantSheaf operationOrdinaryAdjunction
  Adjunction.leftAdjointUniq

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  SheafOfModules.restrictScalars integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose completedAdicCommRing completedAdicCommPresheaf
  SheafOfModules.QuotientIsoTransport.transport completedAdicFiniteModule
  completedAdicFiniteCommRing completedAdicFiniteCommPresheaf completedAdicCommProjection
  completedAdicOrdinaryTower completedAdicModules_monoidal SheafOfModules.monoidalCategory

section ScalarTensor
universe a b r
variable {X : Type a} [Category.{b} X] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology X}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

end ScalarTensor

attribute [local irreducible] tensorModelIso
  SheafOfModules.QuotientIsoTransport.ordinaryScalarSquare
  SheafOfModules.QuotientIsoTransport.scalarRestrictionSquare

attribute [local implicit_reducible] coefficientTransport

attribute [local irreducible] adicScalarModel integralScalarModel

end WeilConjectures
