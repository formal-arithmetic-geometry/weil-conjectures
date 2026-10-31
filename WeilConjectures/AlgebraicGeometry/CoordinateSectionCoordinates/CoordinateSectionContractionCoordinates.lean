/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionTateCoordinates

/-! # The actual line contraction in ordinary coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one calculation and
finite etale-origin transport (blueprint: lem-pur-coordinate-section-contraction-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateSectionCoordinates
open AffineZeroPurity AffineSpacePurity AffineLinePurity VectorIntegrationSite
open CoordinateSectionNormalization

/-- The tower's chosen line comparison and exceptional contraction agree with
the ordinary normalization's gammaCoordinates and proComposition.

Source: current blueprint, finite-site transport sentence and the final
identification of gamma with the transpose of the affine-line adjunction
(blueprint: lem-pur-coordinate-section-contraction-coordinates).

Proof: expand targetLineGamma and supportedTargetComparison. Naturality of the
integration-transposed line comparison moves tateComparison from the input
through the line source and the exceptional target. The sourceCoordinates and
sourceComparison factors cancel, leaving gammaCoordinates with the retained
ordinary Tate input. For the contraction, expand compositionInverse and the
identity-normalized identityUnit. Transport the compact-support compositor to
the ordinary site using compactSupportSiteCoherence. Uniqueness of right
adjoints and mate pasting identify the resulting right comparison with the
closed ordinary exceptionalComposition. Its intermediate ordinary/pro-etale
comparison unit is precisely middleUnit, whose given inverse cancels that
unit. The outside comparison counit is the one in proComposition. The
adjunction triangle identities cancel the remaining units and counits, giving
the displayed literal equality. This is a comparison of contraction maps only:
no Cartier map, orientation or evaluation equation is used. The identity
normalizations include r=0, and the empty base is harmless. -/
theorem lineContraction_coordinates
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (hM : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (setting P n).Coefficient) (iteratedAffineLine B r)
      (input P n (iteratedAffineLine B r) r))
    (hplus : DerivedCategory.TStructure.t.plus
      ((comparison (setting P n).Coefficient (iteratedAffineLine B r)).obj
        (input P n (iteratedAffineLine B r) r)))
    (hunit : IsIso (middleUnit (setting P n).Coefficient (iteratedAffineLine B r)
      ((comparison (setting P n).Coefficient (iteratedAffineLine B r)).obj
        (input P n (iteratedAffineLine B r) r)))) :
    (orientationTargetComparison P n B aB r).inv ≫
      (rightDerivedUpperShriek (setting P n).Coefficient (lastSection B r)).map
        (CoordinateTowerNormalization.targetLineGamma P n B aB r) ≫
      CoordinateTowerNormalization.lineCollapse P n B aB r ≫
      (tateComparison P n (iteratedAffineLine B r) (towerBase aB r) r).inv =
    (proClosed (setting P n).Coefficient (iteratedAffineLine B r)).map
      (gammaCoordinates (iteratedAffineLine B r) (setting P n) (setting P n).level
        (annihilates (setting P n)) (towerBase aB r)
        (input P n (iteratedAffineLine B r) r) hM hplus) ≫
      proComposition (setting P n).Coefficient (iteratedAffineLine B r) _ hunit := by
  sorry

end AlgebraicGeometry.ProEtale.CoordinateSectionCoordinates
