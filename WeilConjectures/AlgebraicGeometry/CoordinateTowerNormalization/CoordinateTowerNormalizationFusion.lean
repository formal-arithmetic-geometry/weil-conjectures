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

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization

namespace AlgebraicGeometry.ProEtale.CoordinateTowerNormalization

/-- The local successor contraction for the ordered normalization.
Source: normalization-induction proof Steps 2, 3 and 5
(blueprint: lem-pur-coordinate-tower-normalization-fusion).
Proof: expand normalization at the positive stage and the four-arrow recursion
for gamma. Naturality of the affine-line comparison moves gamma_r across the
line comparison, with W_r and the recorded stageEtale antecedent as its two
finite-Tor inputs. The stepSource factors cancel the targetSourceIso factors.
Naturality moves the closed inverse compositor across the resulting map.
Apply associativity of originComposition to z_r,s_r,q_r,p_r, use s_r q_r=id
and z_r p_r=id, and conjugate the equality through the pasted adjunctions.
This identifies contracting the outer composite with first contracting s_r q_r
and then z_r p_r. Naturality of the first contraction at gamma_r gives exactly
the displayed formula. The zero-stage normalizationRaw and identityCompositeMap
supply the same identity-unit factors, so r=0 is included. No orientation, its
invertibility, induction hypothesis, or terminal normalization is assumed. -/
theorem normalization_fusion
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (r : ℕ) (hline : LineLaw P n B aB (r + 1)) :
    closedCompositionInverse P n B aB r ≫ normalization P n B aB (r + 1) =
      (rightDerivedUpperShriek (setting P n).Coefficient
        (zero B r)).map
          ((rightDerivedUpperShriek (setting P n).Coefficient
            (lastSection B r)).map (targetLineGamma P n B aB r) ≫
              lineCollapse P n B aB r) ≫ normalization P n B aB r := by sorry

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
