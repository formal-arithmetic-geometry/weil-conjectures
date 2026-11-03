/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularProjectionClass

/-! # Kummer sign of the normalized affine projection

Source: sk-thm-regular.proof.md, Step 4(iii), the projective-line normalization
and its ordered exterior product.
(blueprint: lem-pur-regular-projection-kummer-sign).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Contracting a normalized affine projection gives the signed ordered coordinate
Kummer class. There is no absolute smooth orientation or general regular immersion
in this statement.

Proof: for one affine coordinate use its projective-line compactification. Under the
specified localization boundary, the supported Kummer boundary of the coordinate is
minus its Cartier class, while the projective-line trace sends the Cartier class to
one. The counit transpose therefore contracts the Kummer boundary to minus the unit.
The diagonal/Rees normalization of the projection agrees with this ordered affine
integration, by the normalization at t=1 in standard coordinates. For c coordinates
factor the projection into c affine-line projections. Apply the projection formula
and the actual compact-support compositor at each step. The co-projection and
inverse-Tate evaluation coherences give the ordered tensor product of the rank-one
contractions. The shifts are even, so no permutation sign is introduced; the scalar
is the product of c minus signs. The supported cup product defining the ordered
Kummer class is this same tensor product under the exceptional adjunction. Translate
back through supportedClassMapEquiv, and transport from the zero section to the
coordinate zero locus by its counit-normalized support isomorphism. For c=0 both
products are empty and the exceptional and tensor unitors give the coefficient unit.
The argument uses scalar extension of the same root sheaf for arbitrary finite Λ;
it does not choose a primitive root, a basis, or a DVR realization. Empty base
schemes and the zero coefficient ring satisfy the same identities.
Source: sk-thm-regular.proof.md, Step 4(iii), and the signed normalization in
cor-pur-affine-space-zero-section-purity
(blueprint: lem-pur-regular-projection-kummer-sign). -/
theorem regularProjectionSupportedClass_eq_signed_kummer
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]
    (B : Scheme.{u}) [IsNoetherian B] (c : ℕ)
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B)]
    (α : dualizingComplex Λ (𝔸(ULift.{u} (Fin c); B) ↘ B) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin c); B) c)⟦2 * (c : ℤ)⟧)
    (hα : regularProjectionOrientationNormalized Λ B c α) :
    regularProjectionSupportedClass Λ B c α = ((-1 : ℤ) ^ c) •
      kummerBoundaryProduct Λ (fun j : Fin c ↦ AffineSpace.coord B (ULift.up j)) := by
  sorry

end AlgebraicGeometry.Etale
