/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.PrincipalReductionConeCalculus
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.PrincipalReductionDerivedNormalization
import WeilConjectures.AlgebraicGeometry.PrincipalConeTensorNormalization
import WeilConjectures.Algebra.Homology.ReductionIsoShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealizationSupplement
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.SixFunctors.IntegralTensorInverseImage

/-!
# Integral extension by zero and localizing closures

Source: blueprint, sec-six-functors-basics/sk-prop-proper-image-localizing,
`sk-cor-int-compactness-ii-extension-zero.md`, assertions (1)--(3); Stacks Tag 09BP
(blueprint: det-cor-int-compactness-ii-extension-zero).

The integral and finite coefficients are the continuous condensed rings of the recorded
completion interface. Positive reduction level n+1 is indexed by n : ℕ. Constructibility
means bounded constructible internal-module cohomology, without a completeness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Extension by zero preserves integral constructibility and its localizing closure.
The reduction assertion is an isomorphism of functors into the actual finite-coefficient
module derived category, rather than just an isomorphism of underlying abelian sheaves.
All sums and limits have the fixed small indexing universe u+1.

Source: blueprint, sec-six-functors-basics/sk-prop-proper-image-localizing,
`sk-cor-int-compactness-ii-extension-zero.md`, assertions (1)--(3); Stacks Tag 09BP
(blueprint: det-cor-int-compactness-ii-extension-zero).

Proof:
1. The module extension by zero is exact and left adjoint to pullback. Its termwise
   derived functor is triangulated. The adjunction preserves all sums, which are
   computed termwise in the unbounded derived module categories.
2. The setting makes X quasi-compact and quasi-separated. Apply the open-extension
   products lemma to the integral coefficient ring and its pullback to U. Exactness
   also preserves equalizers, so products give preservation of every small limit.
3. Exact integral-linear extension by zero commutes with the scalar map pi^(n+1)
   and its cone. The principal-reduction cone calculus identifies this cone with
   derived extension to the finite quotient. This gives the natural reduction
   isomorphism at every positive level.
4. Apply bounded-constructibility preservation for open extension with the condensed
   coefficient ring O_E, or equivalently the open-extension clause of integral tensor.
5. The inverse image of Loc(Dbc(X,O_E)) under j_! is replete, triangulated and closed
   under all small sums by steps 1--2. By step 4 it contains Dbc(U,O_E). Minimality
   of its localizing closure proves the last assertion. No completeness is imposed
   on either localizing closure. -/
theorem integralOpenExtension
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] [QuasiCompact j.left] :
    PreservesFiniteLimits (openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left) ∧
    PreservesFiniteColimits (openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left) ∧
    (D(openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left)).IsTriangulated ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      D(openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left)) ∧
    PreservesLimitsOfSize.{u + 1, u + 1}
      (openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left) ∧
    (∀ n : ℕ, Nonempty
      (D(openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left) ⋙
          AdicCompletion.derivedReduction l E X.left n ≅
        AdicCompletion.derivedReduction l E U.left n ⋙
          D(openImmersionLowerShriek (DerivedNakayama.quotientRing l E (n + 1)) j.left))) ∧
    (boundedConstructible (AdicCompletion.ring l E U.left) ≤
      (boundedConstructible (AdicCompletion.ring l E X.left)).inverseImage
        D(openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left)) ∧
    (localizingClosureOfSize.{u + 1}
        (boundedConstructible (AdicCompletion.ring l E U.left)) ≤
      (localizingClosureOfSize.{u + 1}
        (boundedConstructible (AdicCompletion.ring l E X.left))).inverseImage
          D(openImmersionLowerShriek (DerivedNakayama.integerRing l E) j.left)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
