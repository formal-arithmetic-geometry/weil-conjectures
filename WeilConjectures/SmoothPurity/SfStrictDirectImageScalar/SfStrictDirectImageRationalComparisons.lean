/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageRationalData

/-! # Assembly of the explicit raw rational direct image

Source: strict direct-image scalar comparison, Step 8.
(blueprint: lem-sf-strict-direct-image-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.SfStrictDirectImageScalar
attribute [local irreducible] HasComparisonLaws IsRationalMaps
  sfIntegralConstructible HasDerivedCategory.standard
  completedOrdinaryScalarExtension completedOrdinaryScalarComplex
  completedScalarChangeData completedScalarComparison completedDerivedScalarExtension
  integralUnit sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage transition associator unitor)

/-- Rational comparisons on the explicitly constructed tensor-Hom direct image.
Source: scalar-comparison proof, Step 8; raw semilinear scalar localization.
(blueprint: lem-sf-strict-direct-image-rational-comparisons)

Proof:
Extend the integral image on Hom modules by tensoring its linear map. This is
rationalImage, and the baseChange pure-tensor formula gives its specified maps.
Localize the integral shift comparisons, including their zero and addition laws.
Both localization composites have the same object map and send g to one tensor I(g),
so the localization comparison is the identity and respects the localized shifts.
Localize the integral comparison components and inverses to obtain theta. Naturality
holds on pure tensors by integral naturality and the image of the scalar, hence on
all tensors by additivity. The source uniformizer is invertible in the target field,
so these semilinear maps are well-defined. Localize the supplied integral unit,
cocycle and shift equations. The prescribed rational units and associators are the
localized integral ones, including the coefficient transports. These equations give
all clauses of HasComparisonLaws for the specified functor, without adding objects
or choosing idempotent splittings. -/
theorem strictDirectImageRationalComparisons {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) (hD : HasIntegralLaws l Ω f D)
    (hcoh : HasIntegralCoherence l Ω f D) :
    ∃ R : Comparisons l Ω f D,
      (∀ E : Index l Ω, R.rational E = rationalImage l Ω f D E) ∧
        HasComparisonLaws l Ω f D R := by sorry

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.SfStrictDirectImageScalar
