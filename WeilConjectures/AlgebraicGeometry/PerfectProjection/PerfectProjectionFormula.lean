/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.IdentityProjectionCompactification.ProjectionFormulaIdentityCompactification
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateSlicePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedRestrictionLocalIso
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
meta import Mathlib.Lean.Meta.CongrTheorems
meta import Mathlib.Tactic.Set
meta import Mathlib.Util.TermReduce

/-!
# Perfect projection formula for completed coefficient reductions

Source: Weil conjectures blueprint, proper base change, order 1275; Stacks Project,
Cohomology on Sites, Tags 0B56 and 0944, and More on Algebra, Tag 0657
(blueprint: lemma-weil-pbc-perfect-projection-formula).

The completed ring is presented as the limit of constant finite quotient sheaves.
The recorded finite-coefficient comparisons identify this presentation with the
continuous-functions presentation, including its quotient maps. Tensors and derived
categories are ordinary and uncompleted. Natural numbers index positive exponents n+1.
-/

@[expose] public noncomputable section

set_option Elab.async true
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
-- Avoid scanning the large representative tactic states for unused tactics.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 30000]
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 2000] CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape
  CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.PerfectProjection

attribute [local instance 3000] completedCommRingWeakSheafify completedCommRingLimits

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (aY : ProEtaleTensorModel Y (ring d Y))
  (aX : ProEtaleTensorModel X (ring d X))
  (K : derived d X)

attribute [local irreducible] coefficients SheafOfModules.monoidalClosed_kfg
  SheafOfModules.monoidalCategory
  CategoryTheory.tensorAdjunctionTotalInverse CategoryTheory.tensorAdjunctionTotal

variable {n : ℕ} (r : Resolution d (X := X) (Y := Y) K n)

attribute [local irreducible] proEtaleOrdinaryTensorPullback

section TotalizationProof

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleRingDerivedPullbackFactors

-- Avoid repeated inspection of the large representative tactic contexts.
end TotalizationProof

-- The explicit intermediate objects preserve the native projection-square statement.
-- Keeping its functor compositions visible avoids evaluating derived functor objects.
section QuotientComposition

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors

end QuotientComposition

section BaseChange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)
  (aY' : ProEtaleTensorModel Y' (ring d Y'))
  (aX' : ProEtaleTensorModel X' (ring d X'))

set_option linter.flexible false in
set_option linter.flexible false in
attribute [local irreducible] proEtaleProjectionFormulaMate proEtaleAmbientRingedExchange
  proEtaleCanonicalTensorComparison

-- Avoid repeated inspection of the large native-operation tactic contexts.
end BaseChange

end AlgebraicGeometry.Scheme.PerfectProjection
