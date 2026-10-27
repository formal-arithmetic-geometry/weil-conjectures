/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizedOrdinaryPullbackData

/-! # Identity of normalized scalar-localization comparisons

Source: Stacks Project, Tags 03EL, 0D6D and 07A4; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-localized-ordinary-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (ϖ : PbcIntegralRing l E)

/-- A normalized identity edge has the specified ordinary and derived identity
comparisons, and both delta-identity squares.
Source: Stacks Project, Tags 03EL, 0D6D, 07A4, 06YS and 0G7D.
(blueprint: lem-per-localized-ordinary-identity).

Proof: the supplied completed coefficient identity, inverse-image identity
naturality, and the edge coefficient-unit equation identify the coefficient
map after precomposition by the localization unit. Its universal property
gives coefficient_id. The ordinary identity comparison multiplies the
coefficient into the module after restriction along pullbackId. Its inverse
inserts 1. Balancing, the coefficient identity and the identity-site
adjunction prove the inverse identities and naturality. This is precisely
the ordinary_tensor formula.

The edge ordinary_unit formula and scalar linearity show that both routes
in ordinary_square send e tensor (b tensor m) to e iota_X(b) tensor m,
with the canonical identity-chart restriction. Local inverse-image generators
and sheafification extend the equality to every module section. Derive the
ordinary identity map using flat-term K-flat representatives; the derived
identity comparison has exactly the displayed derived_model equation.
Insert the Edge model equation and the fixed integral derived identity
model equation. The ordinary identity square and cancellation of the
invertible resolving counits prove derived_square on these representatives.
Every unbounded object is isomorphic to such a representative. Naturality
transports the equality along that isomorphism and makes it independent
of the choice. No structural coefficient map is assumed invertible. -/
theorem localizedOrdinaryIdentity_exists (X : Scheme.{u})
    (hc : completedCoefficientMap (𝟙 X) (pbcIntegralDatum l E) =
      (proEtaleRingInverseImageId X).hom.app (B l E X))
    (a : Edge l E ϖ (𝟙 X)) : Nonempty (Identity l E ϖ X a) := by sorry

end AlgebraicGeometry.Scheme.LocalizedOrdinary
