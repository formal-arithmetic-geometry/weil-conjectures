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
import WeilConjectures.AlgebraicGeometry.FinitePointIntegralHeartUpperBound
import WeilConjectures.AlgebraicGeometry.FinitePointRationalHeartUpperBound

/-! Integral and rational heart bounds split from the finite-point range theorem.
Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Complement (blueprint: lem-sf-finite-point-cohomological-range).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The integral and rational constructible-heart estimates.  This is the three
non-finite clauses of `finite_point_cohomological_range`, isolated so that the
integral reduction/Nakayama argument and the two scalar-descent filtrations can
be proved independently.
Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Complement (blueprint: lem-sf-finite-point-integral-rational-heart-upper-bound).

Proof: A constructible integral sheaf has Tor amplitude [-1,0] by the integral regularity
criterion, so direct-image stability and point realization give perfect scalar images. Reduction
modulo the uniformizer has range [-1,0]. The scalar-six comparison identifies the outputs after
finite reduction. Perfectness makes cohomology bounded and finite. If the largest nonzero
cohomology degree i were above 2 dim X, its nonzero quotient modulo the uniformizer (Nakayama)
would contradict the finite-reduction bound. Constructible point evaluation detects zero
cohomology, so both native outputs vanish above 2 dim X.
For an $E$-sheaf, take an ordered common refinement of its lisse strata by the stratified-
lattice theorem. The heart filtration then has quotients $a_!L_0[1/\ell]$; since
$E_S\cong\mathcal O_{E,S}[1/\ell]$ is the colimit of multiplication by $\ell$ and tensor
commutes with colimits, $E_S\otimes_{\mathcal O_{E,S}}L_0\cong L_0[1/\ell]$, underived because
$L_0$ is locally free. Integral extension $a_!L_0$ is constructible in degree zero and has
finite Tor amplitude. The normalized immersion comparison commutes $a_!$ with scalars. Integral
bounds, direct-image scalar comparison and flat localization give $[0,2d]$ for each quotient,
hence for the sheaf by its finite filtration.
For a constructible Qbar sheaf, descend every lisse filtration quotient to a finite extension.
The E bound, exact scalar extension, and immersion and direct-image scalar comparisons give the
upper bound 2 dim X for each quotient. Finite filtrations preserve this range. Zero sheaves and
empty schemes give zero in every degree.
In Lean the first paragraph is `finite_point_integral_heart_upper_bound` and the last two are
`finite_point_rational_heart_upper_bound`; the theorem is their conjunction.
-/
theorem finite_point_integral_rational_heart_upper_bound_split
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ (X : Over (Spec (.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (c : Compactification X.hom)
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.left)),
      IsConstantModelConstructible
        (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.left M →
      ∀ d : ℕ, topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ∀ P ∈ [(rightDerivedLowerShriekOfCompactification
          (DerivedNakayama.integerRing ℓ (ULift.{u} E)) c).obj
          ((DerivedCategory.singleFunctor _ 0).obj M),
        (lowerStar (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.hom).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)],
        P.IsLE (2 * (d : ℤ))) ∧
    (∀ (X : Over (Spec (.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (c : Compactification X.hom)
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left)),
      IsConstantModelConstructible
        (Profinite.continuousMapRingObj.{u} E) X.left M →
      ∀ d : ℕ, topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ∀ P ∈ [(rightDerivedLowerShriekOfCompactification
          (Profinite.continuousMapRingObj.{u} E) c).obj
          ((DerivedCategory.singleFunctor _ 0).obj M),
        (lowerStar (Profinite.continuousMapRingObj.{u} E) X.hom).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)],
        P.IsLE (2 * (d : ℤ))) ∧
    (∀ (X : Over (Spec (.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (c : Compactification X.hom)
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left)),
      IsConstantModelConstructible
        (Profinite.padicAlgClRingObj.{u} ℓ) X.left M →
      ∀ d : ℕ, topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ∀ P ∈ [(rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj.{u} ℓ) c).obj
          ((DerivedCategory.singleFunctor _ 0).obj M),
        (lowerStar (Profinite.padicAlgClRingObj.{u} ℓ) X.hom).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)],
        P.IsLE (2 * (d : ℤ))) := by
  have hI := finite_point_integral_heart_upper_bound D ℓ hℓ E
  have hR := finite_point_rational_heart_upper_bound D ℓ hℓ E
  exact ⟨hI, hR.1, hR.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing
