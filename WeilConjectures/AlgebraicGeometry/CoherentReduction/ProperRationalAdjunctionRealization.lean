/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentMappingSystems
public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteExceptionalDerivedHom
public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteProperReductionTransport
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.CategoryTheory.Adjunction.AdjunctionReductionCounit
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-! # Rationalization of the integral proper adjunction

Source: the finite-E proper-adjoint construction in the current blueprint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall scalarSmallDerived

/-- Rationalizing an integral realization gives the actual rational proper adjunction
and preserves its normalized counit square.
Source: finite-E proper-adjoint proof, inversion of ell; rationalization comparison
(blueprint: lem-sfb-proper-rational-adjunction-realization).

Proof: identify E with a finite subfield of an algebraic closure and transport the
rationalization comparison along this coefficient isomorphism, retaining the
continuous ring topologies and the original coefficient inclusion. This gives the
two scalar localization equivalences and their extension comparisons. The inclusion
O to E is flat, and derived extension restricts to bounded constructible objects.
Integral constructibility agrees with finite Tor constructibility. The canonical
proper scalar mate is therefore invertible on these objects; use that same mate
for scalarComparison, so scalar_spec is its comparison square.

The integral Hom bijection is O-linear by hypothesis. Linearity of the left
functor and its right adjoint follows from the Hom bijections and linear composition.
Extend both functors to raw scalar localization by tensoring their maps with E.
Tensor the unit and counit with one. Naturality holds first on pure tensors by
linearity and then on all morphisms by tensor induction. The triangle identities
are the integral triangle identities tensored with one. Transport this adjunction
through the two rationalization equivalences. Use the proper scalar mate to
identify its left adjoint with the restriction of the actual rational Rp_*.
The equivalence units give lambda on the right adjoint. The counit in these
coordinates is the image of the original counit: expand the transported counit,
move the equivalence units through it by naturality and cancel the equivalence
triangle identities. This gives precisely counit_eq, with scalarComparison and
lambda in the stated order. The construction includes zero objects and the empty scheme.
-/
theorem proper_rational_adjunction_realization
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀]
    (hField : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hSep : ell ≠ p₀)
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [IsProper p]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E]
    (C : Bc ell E Y ⥤ TowerDerived ell E Z)
    (R : ProperTorsionRealization ell E p C) :
    Nonempty (ProperRationalRealization ell E p C R) := by
  sorry

end AlgebraicGeometry.ProEtale.CoherentReduction
