/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.CanonicalIntegralRefinementPastingData
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestriction

/-! # The normalization equation of one integral refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Rewrite the normalization of one integral refinement in the canonical integral category.

Source: `RingRefinementNormalized`, the open-unit transpose normalization, and the
canonical proper-push compositor in the integral normalized pasting argument.
(blueprint: lem-sf-normalized-integral-refinement-bridge).

Proof: Unfold the normalization predicate and the concrete pasting-data record.
Let ε₀ be the chosen open comparison, whose transpose is recorded in that record.
Unfold the canonical operation, refinement and left-realization wrappers,
retaining exactly the supplied data of `R` and `N`.
Extract `hi`, `hg`, and the pointwise comparison `ε` from `N.refinement_normalized`.
The canonical refinement restriction is the component of an invertible natural
transformation (`exists_refinementRestriction`). Apply the open adjunction Hom
bijection to `ε.hom` and to `ε₀.hom.app K`. Their normalized transposes become the
same open-unit component after composition with that invertible restriction.
Cancel the restriction and use injectivity of the Hom bijection to obtain
`ε = ε₀.app K`. The completed geometric push compositor equals `ringedPushComp`:
both are the conjugate, under the same derived adjunctions, of the canonical
completed pull compositor; the coefficient-composition witnesses are proof
irrelevant. Substitute these two equalities in the recorded normalization.
Precompose that equality with `(R.left c (.integral E)).hom.app K` and cancel its
inverse. Associativity gives exactly the asserted equation. This argument applies
to an individual refinement and an arbitrary input; it uses no composition law
for refinements, no finite evaluation criterion, and no absolute separatedness. -/
theorem normalized_integral_refinement_bridge
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType (X.left ↘ Spec (.of D.k))]
    [QuasiCompact (X.left ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of D.k))]
    [QuasiCompact (Y.left ↘ Spec (.of D.k))]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f.left))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (E : FieldStage.{max u v} l) :
    IntegralSystemRealization.IntegralRefinementPastingData.Normalized l E.carrier D hl f
      (canonicalIntegralRefinementPastingData l Ω D hl f R F M N E) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
