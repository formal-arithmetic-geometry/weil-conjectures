/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationData

/-! # Local coordinate-tower normalization step

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
open AffineZeroPurity AffineSpacePurity VectorIntegrationSite
attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
  originCompositionAmbient derivedComparisonAdjunction

/-- The fixed exceptional tower compositors are invertible.
Source: normalization-induction proof Steps 2, 3 and 6
(blueprint: lem-pur-coordinate-tower-exceptional-compositors).
Proof: restrict the exceptional adjunctions to bounded-below etale-origin objects.
Their composite is an adjunction, with the pasted counit. Conjugate the canonical
originCompositionAmbient isomorphism. Its component is compositionInverse: both
are the unique transpose of that pasted counit. The conjugate is invertible.
At stage zero exceptionalCompositeRaw instead uses identityCompositeMap, an
isomorphism induced by equality of scheme morphisms. Its defining HEq identifies
exceptionalComposite with that map. At positive stages use compositionInverse.
The closed-composition arrow is compositionInverse followed by equality transport
along zero_successor; hence it too is invertible. These statements concern no
orientation or normalization identity. At r=0 they use the identity normalization;
on an empty scheme the same adjunction argument applies. -/
theorem exceptionalCompositors_isIso
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    IsIso (exceptionalComposite (setting P n) B aB
      ⟨coefficientUnit P n B, (unit_origin P n B).plus⟩ r) ∧
    IsIso (closedCompositionInverse P n B aB r) := by sorry

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
