/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SixFunctors.Supporting.SpecifiedPullbackComparisonAlpha
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.PoincareDuality.Pod.PodCounitScalarWordCoordinates
import WeilConjectures.PoincareDuality.ExplicitScalarCone.ExplicitScalarConeWordCoordinates

/-!
# Agreement of the specified integral pullback scalar comparisons

For an isomorphism of schemes, the scalar comparison built from whole-system counits agrees with
the specified tensor-and-completion comparison.

## Implementation details

Both comparisons are computed in simultaneous normalized quotient models with the actual quotient
transitions, using the same K-flat terms as `specifiedPullbackComparisonAlpha`; effectivity makes
all intermediate counits invertible. With source and target word-realization isomorphisms
`β_A`, `β_B`, the counit-built map `a` satisfies `β_B ≫ a = L(κ) ≫ β_A`
(`podCounitScalarWordCoordinates`), and the balanced scalar association map shows that the
tensor-and-completion comparison satisfies the same equation
(`ExplicitScalarCone.explicitScalarConeWordCoordinates`). Cancelling `β_B` gives the agreement.
No finite quotient flatness or finite Tor-amplitude assumption is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
namespace WeilConjectures

/-- For an isomorphism `g` and a constructible integral object `K`, the whole-system counit
scalar comparison `integralComparisonScalar l E L ι D g K` equals the specified
tensor-and-completion comparison `scalarPullbackCompleted`, as morphisms in the ambient derived
category. -/
theorem isomorphismScalarComparisonAgreement
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonScalar l E L ι D g K).hom =
      (scalarPullbackCompleted l E L ι g K.obj K.property.1
        (specifiedPullbackComparisonAlpha l E L ι g K.obj K.property).choose).hom := by
  let e : CounitRealization.Coefficient.{u} l := ⟨E, inferInstance, inferInstance, inferInstance⟩
  let f : CounitRealization.Coefficient.{u} l := ⟨L, inferInstance, inferInstance, inferInstance⟩
  have h := (podCounitScalarWordCoordinates l).2 D e f ι g
  have hα := ExplicitScalarCone.explicitScalarConeWordCoordinates l E L ι g
    ((D.coefficient E).system Y) ((D.coefficient E).system X)
    ((D.coefficient L).system Y) ((D.coefficient E).roos X)
    ((D.coefficient L).roos X) ((D.coefficient L).roos Y)
    ((D.coefficient E).pullback g) ((D.coefficient L).pullback g)
    ((D.scalar E L ι).model X) ((D.scalar E L ι).model Y)
    ((D.coefficient L).system X) K.obj K.property
    (h.initial K) (h.pullback K) (h.scalar K) (h.sourceWord K) (h.targetWord K)
  have hβ := (h.coordinates K).2
  apply (cancel_mono (podCounitScalarBetaB l D e f ι g K.obj)).1
  rw [h.comparison K]
  simpa only [podCounitScalarBetaA, podCounitScalarBetaB,
    CounitRealization.Primitive.comparison, CounitRealization.Primitive.model,
    CounitRealization.Primitive.system, podCounitWordModels,
    ExplicitScalarCone.betaA, ExplicitScalarCone.betaB,
    ExplicitScalarCone.pullbackSystem, ExplicitScalarCone.scalarSystem,
    ExplicitScalarCone.sourceSystem, ExplicitScalarCone.targetSystem,
    Category.assoc] using hα.symm

end WeilConjectures
