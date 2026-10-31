/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.CoordinateTailProductPullback
import WeilConjectures.AlgebraicGeometry.CoordinateSuccessorCupProjection

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

/-- The supported coordinate product satisfies the last-section recursion.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, parent proof Steps 1--4.

Proof: use the affine tower presentation at ranks `r` and `r+1`.  Pullback of
the first `r` Cartier boundaries identifies their ordered cup with the pullback
of `compactProduct r`.  The final boundary is the rank-one supported cup along
`lastSection`.  The counit-defined projection map agrees with coefficient
multiplication on the intersection, and its naturality moves the pulled-back
`compactProduct r` through the projection.  The defining projection equation of
`sectionArrow`, the canonical source compositor `coordinateComposition`, and
the normalized tensor multiplication then give the displayed equality.  The
finite Tate line is locally free, so the projection component is invertible;
all shifts are even, hence the reordering sign is one.  The argument is valid
for empty bases as well.
(blueprint: lem-pur-coordinate-supported-product-successor)
-/
theorem coordinate_supported_product_successor (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    compactProduct P n B aB (r + 1) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r := by
  let := zero_exact P n B aB r
  let := zero_exact P n B aB (r + 1)
  rw [compactProduct_eq P n B aB (r + 1), supportedClass_successorCup,
    ← coordinate_tail_product_pullback P n B aB r]
  refine (coordinate_successor_cup_projection P n B aB r
    (supportedClass P n B aB r)).trans ?_
  exact congrArg (fun f ↦ (coordinateComposition P n B r).hom ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (lastSection B r)).map f ≫ sectionArrow P n B aB r)
    (compactProduct_eq P n B aB r).symm

end AlgebraicGeometry.ProEtale.AffineZeroPurity
