/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateTailProductPullback
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCupProjection

/-! # Successor supported coordinate product recursion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

private theorem compactProduct_eq (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := zero_exact P n B aB c
    compactProduct P n B aB c =
      (closedSingleIso (setting P n).Coefficient (zero B c)
        ((setting P n).constant B)).hom ≫ supportedClass P n B aB c := by
  let := zero_exact P n B aB c
  let := tower_noetherian (setting P n) B aB c
  unfold compactProduct thom coordinateThomAdjunct
  exact (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).symm_apply_apply _

end AlgebraicGeometry.ProEtale.AffineZeroPurity
