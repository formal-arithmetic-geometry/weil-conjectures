/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
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
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Total tensor and ordinary scalar reduction, with their actual units

Source: Stacks Project, Tags 03EK, 06YY and 012Z.
(blueprint: lem-a1-quotient-tensor-scalar-tower-comparison).
The proof first constructs the balanced scalar comparison on sheaves, then lifts it
through degree-zero totalization, and checks the transition and unit formulas.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ChangeOfRings
namespace SheafOfModules
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
open RestrictedTensorProof
attribute [local implicit_reducible] SheafOfModules.restrictScalars SheafOfModules.unit
  CategoryTheory.sheafCompose siteSheafTensorRight

attribute [local irreducible] moduleTensorScalarIso swapSheafIso
  siteSheafTensorRightIso tensorObjIsoSheafification

end SheafOfModules

namespace SheafOfModules
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.sheafCompose
end SheafOfModules

universe t u
namespace WeilConjectures
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  IntegralOnSlice.finite IntegralOnSlice.projection
  PrincipalKoszulStrictReplacement.residue SheafOfModules.restrictScalars SheafOfModules.unit
  completedIntegralCommRingProjectionUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  IntegralOnSlice.reductionWitness IntegralOnSlice.reduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : AlgebraicGeometry.Scheme.{t})
open SheafOfModules SheafOfModules.RestrictedTensorProof
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory

section TensorProof
variable [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  PresheafOfModules.unit SheafOfModules.changeOfRingsPresheaf
  ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'

attribute [local implicit_reducible] tensorWith targetTower targetTowerMap
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.ofOpSequence
  CategoryTheory.Functor.ofSequence

attribute [local implicit_reducible] tensorMonoidal
  KFlatTotalTensorModel.tensor KFlatTotalTensorModel.monoidal
  CategoryTheory.Functor.mapHomologicalComplex CochainComplex.singleFunctors

attribute [local irreducible] residueCoefficientIso

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

attribute [local irreducible] sliceSwapIso

attribute [local irreducible] tensorScalarLevelIso

section GeneratorChecks
attribute [local implicit_reducible] IntegralOnSlice.tower IntegralOnSlice.level

end GeneratorChecks
end TensorProof

end WeilConjectures
