/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalizationData

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

/-- The compact transpose identity for an arbitrary zero-section arrow.
Source: normalization-induction proof Steps 7 and 8
(blueprint: lem-pur-coordinate-tower-compact-transpose).
Proof: expand augmentation and the inverse exceptional Hom equivalence as the
compact direct image of the arrow followed by the exceptional counit. Replace
the proper direct-image identification by its canonical inverse. Naturality of
the closed counit moves the supplied arrow to the right. The composite counit
formula and the defining transpose of compositionInverse then replace the two
counits by the counit of p_r z_r. Equality transport p_r z_r=id and the canonical
compact identity comparison give sourceIdentification. What remains on the
right is the supplied arrow followed by normalization. At r=0 unfold the
identity versions projectionGammaRaw and normalizationRaw; their identityUnit
factors cancel. No evaluation identity or orientation is used, and the arrow
need not be invertible. This also covers the empty base. -/
theorem compact_transpose
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (t : ThetaHom P n B r) :
    letI : IsNoetherian (iteratedAffineLine B r) :=
      tower_noetherian (setting P n) B aB r
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (iteratedAffineLineProj B r)).map
        ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).inv.app
            (coefficientUnit P n B) ≫
          (rightDerivedUpperShriekHomEquiv (zero B r) (unit_origin P n B)
            (target_plus P n _ (towerBase aB r) r)).symm t) ≫
      augmentation P n B aB r =
        (sourceIdentification P n B aB r).hom ≫ (t ≫ normalization P n B aB r) := by sorry

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
