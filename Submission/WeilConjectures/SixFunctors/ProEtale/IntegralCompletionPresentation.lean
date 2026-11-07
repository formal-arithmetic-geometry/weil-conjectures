/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDifferential
public import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Submission.WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import Submission.WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import Submission.WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import Submission.WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralPresentationEncoding
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Submission.WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import Submission.WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical completeness in the completed integral presentation

Stacks Project, Tags 06YY, 0941, 08TC and 0145
(auxiliary; not a blueprint node).

The coefficient identification is normalized by every finite restriction square.
Finite comparisons retain their finite coefficient action.
Their restriction squares are normalized on underlying abelian sheaves, and their
units fix the derived comparisons uniquely. The index n denotes exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u d

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (A : Encoding l E X)

/-- The existing finite continuous-to-constant encoding, at exponent n+1.
Source: blueprint integral-limit and finite-coefficient conventions; Stacks 00YV
(auxiliary; not a blueprint node). -/
abbrev FiniteEncoding (n : ℕ) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X

end AlgebraicGeometry.ProEtale.IntegralPresentation
