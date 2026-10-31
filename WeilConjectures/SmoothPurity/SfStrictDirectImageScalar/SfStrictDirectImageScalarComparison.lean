/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarData
import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageIntegralModels
import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageIntegralComparisons
import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageRationalComparisons

/-! # Scalar compatibility of the strict-tower direct image

Source: blueprint strict direct-image scalar comparison, Steps 1--8.
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
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfStrictDirectImageScalar
attribute [local irreducible] HasDerivedCategory.standard
  completedOrdinaryScalarExtension completedOrdinaryScalarComplex
  completedScalarChangeData completedScalarComparison completedDerivedScalarExtension
  integralUnit sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
/-- Scalar compatibility for the specified strict-tower integral direct images and
raw rationalizations, with all the displayed normalized maps retained.

Source: blueprint, sec-smooth-purity/sk-prop-sf-closed-unit, rational and algebraically
closed scalar-comparison paragraphs; Stacks 0D6E and 0A07
(blueprint: lem-sf-strict-direct-image-scalar-comparison).

Proof:
1. Finite-type schemes over k are Noetherian and finite-dimensional, and l remains
invertible on them. Apply prop-weil-pbc-scalar-extension. Integral direct-image
constructibility gives bounded constructible outputs. Use the normalized reconstruction
of lem-pur-completed-coefficient-pushforward-comparison on strict derived diagrams,
as specified by lem-weil-derived-direct-image-composition. Integral scalar extension
preserves these full subcategories by lem-weil-integral-scalar-extension-constructible.
2. The ambient image is additive and linear by
lem-sbc-completed-operations-linear-natural-exchange. Conjugating it by reconstruction
proves additivity, linearity, and compatibility of reconstruction with constant scalars.
3. Write beta for the ordinary completed scalar/direct-image comparison, with its
counit-tensor normalization. Conjugate its inverse by chi on the two sites, and then
by reconstruction on the two coefficient fields. This is integral_normalization;
finite-free-completed-scalar-comparison makes every factor invertible.
4. For three fields, lem-fix-scalar-completion-associator identifies A_S h with
chi A_C. Expand the three conjugates, move chi past beta by naturality, and cancel.
The result is precisely the inverse ambient scalar cocycle. The unit calculation
uses the multiplication/completeness units. The tensor associators agree with the
prescribed scalar associators by lem-pur-completed-line-tensor-coherence.
5. Substitute the reconstruction conjugates. Adjacent reconstructions and inverses
cancel. Naturality of the scalar associator and reconstruction gives the integral
cocycle and the identity-extension comparison.
6. Reconstruction commutes with the specified shifts: its augmentation has quotient
maps in the unshifted product coordinate and zero in the shifted coordinate by
lem-trf-completion-unit-strict-quotient-model. Reindex the first coordinate and keep
the second zero; lem-weil-roos-comm-shift supplies the signed Roos square. For the
remaining derived-composition comparisons compute on K-injectives I,J and j:f_*I→J.
Their maps are g_*j, and shifting gives g_*(j[r])=(g_*j)[r], by
lem-weil-pbc-kinjective-shift and the normalized derived-pushforward compositor.
7. Chi commutes with native tensor and product-cone shifts by
lem-weil-completed-scalar-chain-shift; beta does so by prop-weil-pbc-scalar-extension.
Composition, inverse, and whiskering preserve these squares by
lem-weil-pbc-commshift-nattrans-comp-whisker.
8. Apply lem-pur-semilinear-scalar-localization. The source uniformizer is a unit
times a positive power of the target uniformizer and is invertible in the target
field. Localize every component and equation. The formulas on pure tensors give
all rational morphisms; no objects or idempotent splittings are added. The unit,
cocycle, and shift equations are exactly the asserted ones. -/
theorem strictDirectImageScalarComparison
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (f : Z ⟶ X) [f.IsOver (Spec (.of k))] :
    ∃ D : IntegralComparisons l Ω f, HasIntegralLaws l Ω f D ∧
      ∃ R : Comparisons l Ω f D, HasComparisonLaws l Ω f D R := by
  classical
  have models (e : Index l Ω) : Nonempty (IntegralModel l (Coefficient.{u} l Ω e) f) :=
    strictDirectImageIntegralModel l (Coefficient.{u} l Ω e) k hl f
  let I : ∀ e : Index l Ω, IntegralModel l (Coefficient.{u} l Ω e) f :=
    fun e ↦ Classical.choice (models e)
  obtain ⟨A, c, hc, hcoh⟩ := strictDirectImageIntegralComparisons l Ω k hl f I
  let D : IntegralComparisons l Ω f := ⟨A, I, c⟩
  obtain ⟨R, _, hR⟩ := strictDirectImageRationalComparisons l Ω f D hc hcoh
  exact ⟨D, hc, R, hR⟩

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.SfStrictDirectImageScalar
