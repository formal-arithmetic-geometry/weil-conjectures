/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralReindexingMaps
import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationComparisonDescent

/-! # Integral comparison and common-stage descent

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- Balanced integral reindexing and the realization comparison for one scheme isomorphism.
Source: BS Remark 6.8.15 and HRS Lemma 7.9; the integral and scalar-descent part of
lem-sf-adic-reindexing-core (blueprint: lem-sf-adic-integral-reindexing-descent).

Proof: The functions equation for B identifies its coefficient map with the canonical
continuous coefficient map. Compare the completed integral inclusions by their finite
quotient projections and the rational inclusions by localization. The balanced map sends
`a tensor x` to `B(a) tensor x`; inverse site transport gives its inverse. Its localization
through the scalar-extension cochain counits is the derived comparison, and the universal
counit equation is integralReindexRepresentative. On an integral constructible object,
compose the integral realization isomorphism with the inverse of this comparison and the
inverse of the specified completed-pullback unit. This is the displayed agreement formula.
Naturality of the completion unit proves naturality on integral arrows. Linear extension
then descends through the raw rationalization, since the coefficient map fixes the
uniformizer. The specified common-field equation of both realizations and the scalar
compatibility of the completed-pullback unit identify these components after extending
the finite field. Represent every common-stage arrow at a common finite field and cancel
the transition comparisons to obtain naturality. Larger fields give the same arrow, so
both components and inverse components descend. They remain inverse since that can be
checked on integral representatives. No tensor, identity or composition coherence of
the resulting realization comparison is asserted here. -/
theorem exists_integral_realization_reindexing (D : FiniteFieldDatum.{u})
    (d : ∀ T : GeometricSpace D, SpaceData l D T)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (B : RingReindex l T.base.left g.hom (d T).realization (d U).realization) :
    letI := (d T).units
    letI := (d U).units
    ∃ I : ∀ E, IntegralReindex l T.base.left g.hom B E,
    ∃ c : commonStageDerivedPullback l (PadicAlgCl l) g.hom ⋙
        ordinary l T.base.left (d T).realization ≅
      ordinary l U.base.left (d U).realization ⋙ derivedPull l T.base.left g.hom B,
    ∀ E, integralRealizationAgreement l g.hom (d T).realization (d U).realization
      B E (I E) c := by
  classical
  obtain ⟨I⟩ := exists_integral_reindexing_maps l D d T U g B
  obtain ⟨c, hc⟩ := exists_realization_comparison_descent l D d T U g B I
  exact ⟨I, c, hc⟩

end WeilConjectures.AdicQbarRealization
