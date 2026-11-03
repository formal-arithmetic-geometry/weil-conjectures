/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCup
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
/-! # Concrete coefficient maps for the successor binary cup

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, the ordered exterior product.
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

/-- The canonical map from the newest divisor coefficient to proper section support.
Source: the intersection identification in the ordered exterior-product calculation.
(blueprint: def-pur-coordinate-successor-coefficient-tensor).
Construction: apply the actual support-change map along successorLastCoordinateIso,
then invert the exact closed-single comparison for the last section. -/
def successorLastCoefficient (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B (r + 1))).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
          (inclusion B (r + 1) 0)).obj
            ((setting P n).constant (divisor B (r + 1) 0))) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (lastSection B r)).obj (unit P n (iteratedAffineLine B r)) := by
  letI : PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (lastSection B r)) :=
    zero_exact P n (iteratedAffineLine B r) (towerBase aB r) 1
  exact (cupSingle (setting P n) (iteratedAffineLine B (r + 1))).map
      ((setting P n).functorialCupSupportMap true (inclusion B (r + 1) 0)
        (lastSection B r) (successorLastCoordinateIso B r).hom
        (successorLastCoordinateIso_hom_inclusion B r)) ≫
    (closedSingleIso (setting P n).Coefficient (lastSection B r)
      ((setting P n).constant (iteratedAffineLine B r))).inv

/-- The coefficient part of the binary successor cup.
Source: the coefficient multiplication in the ordered exterior-product calculation.
(blueprint: def-pur-coordinate-successor-coefficient-tensor).
Construction: identify compact support on the total zero section with its degree-zero
closed image. Change support to the full coordinate intersection and expose its cons
presentation. Apply the inverse of the specified derived closed coefficient multiplication;
its invertibility determines this inverse uniquely. -/
def successorBinaryCoefficient (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B (r + 1))).obj (unit P n B) ⟶
      cupTensorObject (setting P n) (iteratedAffineLine B (r + 1))
        ((cupSingle (setting P n) (iteratedAffineLine B (r + 1))).obj
          ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
            (successorTailMap B r)).obj ((setting P n).constant (successorTail B r))))
        ((cupSingle (setting P n) (iteratedAffineLine B (r + 1))).obj
          ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
            (inclusion B (r + 1) 0)).obj
              ((setting P n).constant (divisor B (r + 1) 0)))) := by
  letI := zero_exact P n B aB (r + 1)
  let S := setting P n
  let X := iteratedAffineLine B (r + 1)
  exact (closedSingleIso S.Coefficient (zero B (r + 1)) (S.constant B)).hom ≫
    (cupSingle S X).map
      (S.functorialCupSupportMap true (zero B (r + 1))
        (supportMap B (r + 1) (List.finRange (r + 1))) (supportIso B (r + 1)).hom
        (supportIso_existsUnique B (r + 1)).exists.choose_spec) ≫
    eqToHom (classSource_eq P n B (r + 1) (List.finRange (r + 1))).symm ≫
    eqToHom (congrArg (classSource P n B (r + 1)) (successorTailList_cons r)) ≫
    eqToHom (classSource_cons P n B (r + 1) 0 (successorTailList r)) ≫
    @inv (CupDerivedCategory S X) _ _ _
      (cupDerivedCoefficientMap (hD := cupHasDerivedCategory S X)
        (hDM := cupMonoidal S X)
        (cupCoefficientMap S (successorTailMap B r) (inclusion B (r + 1) 0)))
      (cupDerivedCoefficientMap_isIso S (successorTailMap B r) (inclusion B (r + 1) 0))

/-- Split the total closed coefficient into section and pulled-back old support.
Source: the binary projection-formula calculation in the zero-section proof.
(blueprint: def-pur-coordinate-successor-coefficient-tensor).
Construction: use successorBinaryCoefficient, tensor the inverse tail-pullback comparison
with successorLastCoefficient, and apply the specified tensor symmetry. This construction
uses neither a boundary nor an arbitrary supported input. -/
def successorCoefficientTensor (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B (r + 1))).obj (unit P n B) ⟶
    ((tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1))).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (lastSection B r)).obj (unit P n (iteratedAffineLine B r)))).obj
      ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
        ((cupSingle (setting P n) (iteratedAffineLine B r)).obj
          ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
            ((setting P n).constant B)))) :=
  successorBinaryCoefficient P n B aB r ≫
    ((eqToHom (classSource_eq P n B (r + 1) (successorTailList r)).symm ≫
      (successorTailSourcePullback P n B r).inv) ⊗ₘ
      successorLastCoefficient P n B aB r) ≫
    (tensorSwap (setting P n).Coefficient (iteratedAffineLine B (r + 1)) _ _).hom

end AlgebraicGeometry.ProEtale.AffineZeroPurity
