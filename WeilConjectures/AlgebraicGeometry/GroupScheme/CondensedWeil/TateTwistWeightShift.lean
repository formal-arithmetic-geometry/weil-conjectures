/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeSignedLineFiniteness
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
import WeilConjectures.CategoryTheory.WeilEquivariance
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Connected.Separation
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
import WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbRootTowerPullbackCoherence
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeights

/-! # Weight shift under a Tate twist

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-r-real-linear/
lem-tw-tate-twist-weight-shift.md (blueprint: lem-tw-tate-twist-weight-shift).

The ordinary twist below assembles the existing signed coefficient line and its
root-normalized Weil map. Weights use the native condensed local-return predicates
on actual sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedWeil

/-- Tate twisting shifts punctual purity and mixed upper weight bounds by minus twice
its integer exponent, for a lisse Weil sheaf.
Source: latest blueprint, lem-tw-tate-twist-weight-shift
(blueprint: lem-tw-tate-twist-weight-shift).

Proof:
1. The Tate line is locally free of rank one for every integer exponent
   (det-def-sp-tate-twist-locally-free), including negative exponents by sheaf duality.
   Tensor with it is an additive exact equivalence by
   lem-pur-sheaf-line-evaluation-inverse-pair. Its derived degree-zero value agrees with
   ordinary tensor by lem-pur-line-unbounded-derived-tensor. The tensor Weil map is
   the prescribed one (lem-wf-tate-twist-compatibility). Kernels and cokernels of Weil
   modules are computed on their carriers. Restriction and Cartesian Tate comparison
   (lem-sfb-localized-site-tensor-restriction, det-prop-sfb-cartesian-coefficients-twists)
   show that this tensor preserves lisseness and constructibility; use the finite
   stratification characterization of sk-lem-coefficient-heart.
2. At a closed point of degree m, restrict to an affine neighbourhood over the base
   finite field. The tensor fibre comparison of lem-fd-condensed-fibre-linear-operations
   identifies the local operator with the tensor of the two local operators. Cartesian
   Tate comparison identifies the point line with the actual coefficient Tate line.
   Compatible primitive roots trivialize its finite stages, limits, scalar extensions,
   powers and duals (def-coefficient-twists-detailed); the coefficient unit evaluates
   to Qbar_l (det-pe-condensed-point-coefficients). Its degree-one operator is q^(-n)
   (def-weil-frobenius-coefficient-twists). The iterate-and-return construction
   (def-weil-local-frobenius-trace) makes the degree-m operator q^(-mn).
   Root pullback coherence (lem-amb-root-tower-pullback-coherence) identifies the
   Cartesian map with the specified point Weil map. A basis of the Tate fibre therefore
   identifies the twisted operator with q^(-mn) times the original one.
3. A nonzero scalar c rescales eigenvalues by alpha to c alpha, directly by the
   eigenvector equation (def-weil-frobenius-module-weights), without semisimplicity.
   Here c=q^(-mn), q_y=q^m, and every field embedding fixes rational scalars. Thus
   |iota(c alpha)|=q^(-mn) q_y^(w/2)=q_y^((w-2n)/2), as required by
   def-weil-punctual-weights. This calculation also applies to constructible pure
   sheaves which are not globally lisse. The NativeL2 predicate quantifies over the
   actual section operator, with scalar eigenvalues represented in the standard `ULift`;
   its `down` projection is the scalar seen by the embedding iota.
4. For mixedness take the finite constructible Weil filtration in
   def-weil-punctual-weights. Exact tensor carries each quotient of weight v to its
   twist, pure of weight v-2n by steps 2--3. These weights are at most w-2n.
   The resulting finite filtration proves mixedness. A filtration of length zero
   remains the zero filtration after tensoring.
-/
theorem tateTwist_weight_shift (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D l X₀)
    (_hLisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (n : ℤ) :
    (NativeL2.Pure D l X₀ M iota w →
      NativeL2.Pure D l X₀ (tateTwist D l hl X₀ M n) iota (w - 2 * n)) ∧
    (NativeL2.Mixed D l X₀ M iota w →
      NativeL2.Mixed D l X₀ (tateTwist D l hl X₀ M n) iota (w - 2 * n)) := by
  sorry

end WeilConjectures.CondensedWeil
