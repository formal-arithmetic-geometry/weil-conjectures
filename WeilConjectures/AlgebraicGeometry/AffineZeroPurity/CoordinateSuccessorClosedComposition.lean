/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows

/-! # Closed-single coordinates for the successor source

Source: exact closed direct-image composition in the affine-space zero-section proof.
(blueprint: def-pur-coordinate-successor-closed-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- Compose closed direct images on degree-zero coefficients, then return to the
compact-support source at the last section.

Source: the exact single comparisons in the binary successor-cup argument.
(blueprint: def-pur-coordinate-successor-closed-composition). The construction uses the
actual lowerStar compositor and the canonical exact-single comparisons throughout. -/
def successorClosedComposition (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B (r + 1))).obj (unit P n B) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (lastSection B r)).obj
          ((cupSingle (setting P n) (iteratedAffineLine B r)).obj
            ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
              ((setting P n).constant B))) := by
  letI := zero_exact P n B aB (r + 1)
  letI : PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (lastSection B r)) :=
    zero_exact P n (iteratedAffineLine B r) (towerBase aB r) 1
  let A := (setting P n).Coefficient
  let e := lowerStarCongr (ModuleCat.{u + 1} A)
      (CoordinateTowerNormalization.zero_successor B r).symm ≪≫
    (lowerStarComp (ModuleCat.{u + 1} A) (zero B r) (lastSection B r)).symm
  exact (closedSingleIso A (zero B (r + 1)) ((setting P n).constant B)).hom ≫
    (cupSingle (setting P n) (iteratedAffineLine B (r + 1))).map
      (e.hom.app ((setting P n).constant B)) ≫
    (closedSingleIso A (lastSection B r)
      ((lowerStar (ModuleCat.{u + 1} A) (zero B r)).obj ((setting P n).constant B))).inv

end AlgebraicGeometry.ProEtale.AffineZeroPurity
