/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateZeroBaseChange

/-! # Closed-source comparison in coordinate base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The proper derived closed exchange and the degree-zero coefficient exchange
have identical source identifications.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final rank-one base-change
sentence; parent proof Step 4 (blueprint: lem-pur-coordinate-closed-source-exchange).

Proof: the two zero sections are closed in Noetherian schemes, so their direct
images are exact. Cancel the compact-support-to-proper comparisons from the
definition of closedExchange and the two definitions of closedSingleIso.
For exact closed direct image, the derived base-change mate on the coefficient
single object is the single image of the underived base-change mate, with the
canonical exact pullback and single comparisons. Verify this by transposing:
apply derivedSingleUnit_comp_comparison to the exact closed adjunctions to
identify their single-object units, and use the canonical composition square
of pullbacks to identify the square in the mate. Restricting constants
through this mate commutes with the constant-unit restriction by the adjunction
triangle identities. Since that restriction is epic and exact inverse image
preserves epimorphisms, the underived mate followed by the constant pullback is
the uniquely normalized functorialCupExchange. Apply the single functor and
restore the cancelled proper comparisons. Its inverse form is precisely the
displayed equation, including unitPullback and coordinateSourcePullback.
No purity or exceptional base-change isomorphism is used; empty schemes and
zero coefficients satisfy the same unit and inverse identities. -/
theorem coordinate_closed_source_exchange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    letI := zero_exact P n B aB c
    letI := zero_exact P n B' (g ≫ aB) c
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B' c)).map (unitPullback P n g).inv ≫
        (closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
          (spaceMap g c) (zero_square g c) _ (unit_origin P n B)).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (closedSingleIso (setting P n).Coefficient (zero B c)
            ((setting P n).constant B)).hom =
      (closedSingleIso (setting P n).Coefficient (zero B' c)
        ((setting P n).constant B')).hom ≫ (coordinateSourcePullback P n g c).inv := by
  sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
