/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorCohomologicalBounds
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.Regular.RegularQuotientSelfCohomology
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalAdjacentQuotientTor
import all WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLocalReductionLowerBound
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedConstructibleTowerLocalEffectivity
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionAlgEquiv
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-!
# Levelwise truncations of an adic reduction tower

Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1429;
Stacks Tags 0118, 08J5, 09C1, 09C7, 099M, 099N and 09C2
(blueprint: prop-weil-pbc-levelwise-truncations).

The strict tower and its quotient-linear levels remain distinct. Standard truncations
are Mathlib's canonical functors. The output data retain both exact evaluation comparisons
and the normalization of the entire truncation triangle. Higher Tor vanishing is required
only for normalization, never for the unconditional strict-tower cohomology formulas.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

-- Select the generic standard localizations before trying specialized coefficient instances.
attribute [local instance 2000] reductionRingModulesHasDerivedCategory
attribute [local instance 2000] pbcTowers_hasDerivedCategory

-- Keep the universal scalar-extension witnesses behind their functor/adjunction API.
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction
attribute [local irreducible] pbcDerivedRestrictComp pbcRestrictComp pbcScalarAdjunction
attribute [local irreducible] Functor.mapDerivedCategory completedReductionCoefficient
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint
attribute [local irreducible] pbcComplexCounit pbcExtensionCounit

variable {T d}

variable (T d)

section ReductionTowerPresentation

-- Compare the completed-coefficient aliases without expanding the chosen limit cone.
attribute [local semireducible] completedReductionCoefficient
attribute [local irreducible] CategoryTheory.Limits.limit

section ReductionLaws

end ReductionLaws

end ReductionTowerPresentation

attribute [local irreducible] pbcReductionAdicTower

section ScalarBounds

attribute [local semireducible] completedAdicDerivedChange

end ScalarBounds

open AlgebraicGeometry.ProEtale

section LocalModelBounds
attribute [local semireducible] completedAdicDerivedChange

end LocalModelBounds

section PrincipalReductionProof
attribute [local semireducible] completedReductionCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end PrincipalReductionProof

section ResidueCounterexampleProof
attribute [local semireducible] completedReductionCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end ResidueCounterexampleProof

section IntegralCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end IntegralCoefficients

open AlgebraicGeometry.ProEtale

section OriginNormalizationProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end OriginNormalizationProof

end AlgebraicGeometry.Scheme
