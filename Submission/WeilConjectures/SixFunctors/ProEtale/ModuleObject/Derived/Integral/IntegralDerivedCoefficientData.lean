/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Submission.WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Integral derived coefficient data

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-int-compactness-ii,
coefficient setup used by `det-cor-int-compactness-ii-extension-zero`
(blueprint: def-sfb-integral-derived-coefficient-data).

The declarations below are canonical names for the coefficient ring, its unbounded derived
category on a scheme, and its derived reduction. Their data is delegated to the definitions in
`DerivedNakayamaResolution`; this module introduces no second coefficient construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The condensed integral coefficient ring used by the integral six-functor statements.
Source: coefficient setup in `sk-cor-int-compactness-ii`
(blueprint: def-sfb-integral-derived-coefficient-data). -/
abbrev integralCoefficientRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  DerivedNakayama.integerRing l E

/-- The ordinary unbounded derived category of integral module objects on a scheme.
Source: coefficient setup in `sk-cor-int-compactness-ii`
(blueprint: def-sfb-integral-derived-coefficient-data). -/
abbrev integralDerived (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  DerivedNakayama.Derived l E X

end AlgebraicGeometry.ProEtale.CondensedRing
