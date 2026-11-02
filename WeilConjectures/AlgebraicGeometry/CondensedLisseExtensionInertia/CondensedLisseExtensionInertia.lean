/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.GroupTheory.WeilGroup
public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import Mathlib.CategoryTheory.Functor.FullyFaithful
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.WeilSheaf.MiddleExtension
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.GroupTheory.WeilGroup
import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineGeometricallyIrreducible
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Extension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineIrreducible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Spreading
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.Algebra.Field.Equiv
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleStalkNeighbourhoodSpreading
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Smooth.IntegralClosure
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import all WeilConjectures.ProperBaseChange.CondensedFieldLfpLocalTriviality

/-! # Extending a condensed lisse Weil sheaf across infinity

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-heart/
rem-dl-a1-conventions.md, unramifiedness paragraph; Stacks 0BSM, 0BTD, 0BSW.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia).

The opens are represented inside the standard projective line. The coefficient
objects, Weil pairs, normalized monodromy, and henselian inertia are the published
constructions. The local presentation can be made on the geometric curve: its
inertia is the same geometric inertia as that of the rational point over the finite
field. No arithmetic descent of the Weil sheaf is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- An open of the projective line as a model over the finite field.
Source: standard projective-line charts, def-sc-p1-standard.
(blueprint: lem-dl-a1-condensed-lisse-extension-inertia). -/
abbrev openModel (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens) : Over (Spec (.of D.k₀)) :=
  Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarCongr

set_option maxHeartbeats 200000 in
-- Instantiate the extension condition while keeping the comparison as an argument.
set_option maxHeartbeats 200000 in
-- Keep the canonical comparison in separately checked categorical lemmas.
set_option maxHeartbeats 0 in
-- Elaborate the actual coefficient-module functors and their comparisons.
end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
