/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteOrientationScalarPresentation
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurity
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows

/-! # Ordinary scalar presentations of the ordered supported-product objects

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 3--4
(blueprint: def-pur-finite-product-scalar-presentation).

The fixed-scalar pro-etale presentation is canonically equivalent to the intrinsic
one. All maps below are the published root-generator, scalar-unit and counit mates.
Positive affine coefficient levels are indexed by their predecessors, as in the
published supported-product API; no divisibility by a ramification index is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

/-- The coefficient unit's ordinary presentation, with its exact single comparison.
Source: supported product Step 3
(blueprint: def-pur-finite-product-scalar-presentation). -/
@[irreducible]
def productUnitPresentation (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) :
    ProEtale.AffineZeroPurity.unit P n T ≅
      (comparison (ProEtale.AffineZeroPurity.setting P n).Coefficient T).obj
        (Etale.ordinaryFiniteUnit (ProEtale.AffineZeroPurity.setting P n).Coefficient T) :=
  eqToIso (ProEtale.AffineZeroPurity.unit_single_eq P n T) ≪≫
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P n).Coefficient)
        T).mapDerivedCategorySingleFunctor 0).symm.app _

/-- Canonical comparison of ordered tensor actions under the published site tensorator.
Source: supported products, Step 3
(blueprint: def-pur-finite-product-scalar-presentation). -/
@[irreducible]
def powerPresentation (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A T) (r : ℕ) :
    (ProEtale.AffineSpacePurity.action
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj
        ((comparison A T).obj L)) r).obj ((comparison A T).obj K) ≅
    (comparison A T).obj
      ((ProEtale.AffineSpacePurity.action
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj L) r).obj K) :=
  (ProEtale.AffineSpacePurity.actionPullbackIso
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj L)
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj
      ((comparison A T).obj L)) (comparison A T)
    (fun M ↦ smoothPurityComparisonTensor A T M L) K r).symm

/-- Canonical identification of the ordinary tensor action with the published line.
Source: ordered product Step 3
(blueprint: def-pur-finite-product-scalar-presentation). -/
@[irreducible]
def orderedEtaleActionPresentation (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) : (r : ℕ) →
    (ProEtale.AffineSpacePurity.action
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) r).obj
          (Etale.ordinaryFiniteUnit A T) ≅ line A N hA T r
  | 0 => (eqToIso (compositionEtalePowerZero A N hA T)).symm
  | r + 1 =>
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).mapIso
      (orderedEtaleActionPresentation A N hA T r)).app _ ≪≫
    (eqToIso (compositionEtalePowerSuccessor A N hA T r)).symm

/-- Present the actual supported-product target by the ordinary ordered root power.
Source: supported products, Step 3
(blueprint: def-pur-finite-product-scalar-presentation). -/
@[irreducible]
def productTargetPresentation (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u})
    (r : ℕ) :=
  (ProEtale.AffineSpacePurity.action
    ((ProEtale.AffineSpacePurity.tensor (ProEtale.AffineZeroPurity.setting P n).Coefficient
      T).flip.obj (ProEtale.AffineSpacePurity.shiftedLine
        (ProEtale.AffineZeroPurity.setting P n) T)) r).mapIso
      (productUnitPresentation P n T) ≪≫
  powerPresentation (ProEtale.AffineZeroPurity.setting P n).Coefficient T _ _ r ≪≫
  (comparison (ProEtale.AffineZeroPurity.setting P n).Coefficient T).mapIso
    (orderedEtaleActionPresentation (ProEtale.AffineZeroPurity.setting P n).Coefficient
      (P.coefficients.l ^ (n + 1 + 1))
      (ProEtale.AffineSpacePurity.annihilates (ProEtale.AffineZeroPurity.setting P n)) T r)

/-- Scalar-unit map at the supported-product source.
Source: node proof Step 4
(blueprint: def-pur-finite-product-scalar-presentation). -/
@[irreducible]
def productUnitMap (P : PurityFiniteSetting.{u}) (a b : ℕ) (hab : a ≤ b)
    (T : Scheme.{u}) :
    (proScalar (Etale.cartierCoefficientReduction P.coefficients.l P.extension a b hab) T).obj
      (ProEtale.AffineZeroPurity.unit P b T) ⟶ ProEtale.AffineZeroPurity.unit P a T :=
  presented (Etale.cartierCoefficientReduction P.coefficients.l P.extension a b hab) T
    (productUnitPresentation P b T) (productUnitPresentation P a T)
    ((ordinaryScalar _ T).map (smoothPurityUnitIso _ T).hom ≫
      (Etale.ExceptionalCoefficients.unitIso _ T).hom ≫ (smoothPurityUnitIso _ T).inv)



end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
