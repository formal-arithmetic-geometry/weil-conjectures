/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportCoefficientPresentation

/-! # Identity normalization of the compact-support restriction comparison

Source: Step 5 of the coefficient quotient cocycle proof, and the sectionwise and
K-injective normalizations of the open/proper restriction comparisons.
(blueprint: lem-coef-compact-support-restriction-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The published compact-support restriction square for the identity coefficient map
is the square of the canonical identity restriction comparisons.

Source: Step 5 of `lem-coef-compact-support-quotient-cocycle`, blueprint
`lem-coef-integral-compact-support.proof.md`, finite-level comparison; Stacks Tags 03DI and 0D6E.
(blueprint: lem-coef-compact-support-restriction-identity).

Proof: restriction along the identity acts as the identity on the underlying sheaves.
The ordinary comparison sfOpenCoefficientRestrictionId is the sectionwise identity
transported through the canonical realization equivalence. The unit-normalized
extension-by-zero square for the identity coefficient homomorphism commutes with
these comparisons: apply its adjunction and use the identity on each generator of
extension by zero. Localize this equality termwise. For direct image, use the specified
K-injective normalization: both routes are the identity coefficient restriction map
on the same K-injective representative, followed by the same universal comparison.
Uniqueness of the right-derived comparison extends the equality to every unbounded
object. Whisker the open equality by derived direct image and the proper equality by
extension by zero. Their composite is sfCompactSupportRestriction by definition and
gives the displayed identity. Transport along hq inserts exactly the two eqToIso
comparisons in the statement. No coefficient invertibility or boundedness is needed
for these identity normalization calculations. -/
theorem compactSupportRestriction_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (A : Type u) [CommRing A] [Finite A]
    (q : A →+* A) (hq : q = RingHom.id A) (K : proEtaleDerivedCategory X A) :
    (compactSupportCoefficientComparison c q).hom.app K ≫
        (compactSupportCoefficientResId Y A q hq).hom.app
          ((sfAmbientCompactSupportCandidate A c).obj K) =
      (sfAmbientCompactSupportCandidate A c).map
        ((compactSupportCoefficientResId X A q hq).hom.app K) := by
  sorry

end WeilConjectures
