/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.FinitePointCompactHeartUpperBound
import WeilConjectures.AlgebraicGeometry.FinitePointIntegralRationalHeartUpperBound

/-! # The native cohomological upper bound over the geometric point
Source: latest blueprint sk-lem-finite, Complement
(blueprint: lem-sf-finite-point-cohomological-range).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The upper bound for the two native, uncompleted direct-image functors.
No perfectness, finite generation, duality or categorical equivalence is asserted.
Source: sk-lem-finite, Complement
(blueprint: lem-sf-finite-point-cohomological-range). -/
def FinitePointCohomologicalHeartUpperBound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] : Prop :=
  ∀ (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)),
    IsConstantModelConstructible Λ X.left M → ∀ d : ℕ,
    topologicalKrullDim X.left = (d : WithBot ℕ∞) →
    ∀ P ∈ [(rightDerivedLowerShriekOfCompactification Λ c).obj
        ((DerivedCategory.singleFunctor _ 0).obj M),
      (lowerStar Λ X.hom).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M)],
      P.IsLE (2 * (d : ℤ))

/-- The compact-support part of the heart bound, isolated because the finite ordinary
bound is proved separately.
Source: sk-lem-finite, finite-coefficient Complement
(blueprint: lem-sf-finite-point-cohomological-range). -/
def FinitePointCompactHeartUpperBound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] : Prop :=
  ∀ (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)),
    IsConstantModelConstructible Λ X.left M → ∀ d : ℕ,
    topologicalKrullDim X.left = (d : WithBot ℕ∞) →
    ((rightDerivedLowerShriekOfCompactification Λ c).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * (d : ℤ))

/-- The finite, integral and rational cohomological bound for constructible sheaves in
degree zero. The finite ordinary case is proved separately, so only the finite
compact-support estimate is asserted here. No lower bound or passage to bounded
complexes is asserted here.

Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Complement (blueprint: lem-sf-finite-point-cohomological-range).

Proof: for finite compact supports choose the dense refinement of the given
compactification, whose dimension equals dim X. Exact open extension preserves
constructibility and degree zero. Apply finite_point_finite_ordinary_bound to its
proper structural map. The finite coefficient encodings commute with open extension
by adjunction and with derived proper image; transport the existing etale-origin
compactification comparison through those encodings. It identifies the dense and
original native compact images, carrying the bound to the original compactification.
For integers, reduction modulo the uniformizer is the cone of its action on the sheaf
and has range [-1,0]. Integral constructible sheaves have finite Tor amplitude
by integral_ctf_equals_bc, so both native images are constructible finite-Tor objects
and their scalar sections are perfect by point realization. Scalar-six compatibility identifies
both scalar reductions with
the finite-coefficient outputs. Perfectness gives finite generation and a largest
nonzero cohomology degree.
In that degree scalar reduction cohomology is H^i(P)/pi, nonzero by Nakayama.
Exact scalar sections identify scalar homology with sections of native homology.
Each native homology sheaf is constructible and has finite Tor amplitude over the
DVR, so faithful point realization on its degree-zero complex detects vanishing. Thus the
finite-level upper bound forces i ≤ 2 dim X.
For E-valued sheaves use the ordered stratified-lattice filtration. Its quotients are
locally closed extensions of localized integral lisse sheaves. Their integral models
are in degree zero; scalar comparison and flat localization transfer the integral
upper bound 2 dim X. Finite filtrations preserve it. For Qbar-valued sheaves descend each
lisse quotient to a finite extension, then use exact extension of scalars and the
immersion and direct-image scalar comparisons. For a sheaf placed in degree zero this gives
the upper bound 2 dim X. Zero sheaves and empty schemes vanish in every degree.
-/
theorem finite_point_cohomological_range
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ n : ℕ, 1 ≤ n → FinitePointCompactHeartUpperBound
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) D.k) ∧
    FinitePointCohomologicalHeartUpperBound (DerivedNakayama.integerRing ℓ (ULift.{u} E)) D.k ∧
    FinitePointCohomologicalHeartUpperBound (Profinite.continuousMapRingObj.{u} E) D.k ∧
    FinitePointCohomologicalHeartUpperBound (Profinite.padicAlgClRingObj.{u} ℓ) D.k := by
  have hfinite := finite_point_compact_heart_upper_bound_split D ℓ hℓ E
  have hrest := finite_point_integral_rational_heart_upper_bound_split D ℓ hℓ E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    simpa [FinitePointCompactHeartUpperBound] using hfinite n hn
  · simpa [FinitePointCohomologicalHeartUpperBound] using hrest.1
  · simpa [FinitePointCohomologicalHeartUpperBound] using hrest.2.1
  · simpa [FinitePointCohomologicalHeartUpperBound] using hrest.2.2

end AlgebraicGeometry.ProEtale.CondensedRing
