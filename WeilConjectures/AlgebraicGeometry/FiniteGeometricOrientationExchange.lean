/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeometricPurityFactors

/-! # Base change of the orientation factor of geometric purity

Source: current blueprint sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.md, (1); finite-geometric-purity-mate, Steps 3, 6--7.
(blueprint: lem-pur-finite-geometric-orientation-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Frobenius
variable (P : PurityFiniteSetting.{u})
variable (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
variable [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
variable [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
variable (f₀ : X₀ ⟶ Y₀)
variable [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
variable (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

/-- The inverse diagonal orientation commutes with the actual dualizing exchange,
after tensor pullback and the specified root-normalized source comparison. This
identity contains no theta or exceptional base change at an arbitrary input.
Source: base-change factors (1), equivariance Steps 1--2
(blueprint: lem-pur-finite-geometric-orientation-exchange).

Proof:
1. Retag the source field maps by Spec gamma. geometricPurityRetagging identifies
   the retained compactification and diagonal orientation with the original ones.
2. Use finite_factors, orientation clause, on the retagged Cartesian square.
   The universal property of the Cartesian square gives the unique isomorphism
   from its upper-left scheme to the canonical pullback, commuting with both
   projections. Transport the finite_factors equation along that isomorphism;
   pullback composition and the counit-preserving exceptional comparison identify
   its arrows with the retained self-square. Undo the
   ordinary/pro-etale comparison. The exchange at the coefficient unit, with the
   ordinaryFiniteUnitPullback map, is exactly geometricPurityDualizingExchange.
   finiteGeneralRingSmoothPurity identifies its direct-A orientation with Pi.
3. Tensor this inverse-orientation equation with the pulled-back f* input. The
   tensor-pullback naturality and inverse-image square give geometricPurityTensorSquare.
   Conjugate by the two realization units; these are the units in the definition
   of geometricPurityOrientationFactor.
4. Reassociate the shift. In a primitive-root chart the inverse-image root is
   gamma(zeta); transition compatibility of roots-of-unity pullback identifies
   the finite twist with the reduced integral twist, including ramified E.
   The defining equation of geometricPuritySource is precisely this chart word.
   Its uniqueness removes the choice of chart. Thus the source comparison is b,
   with no scalar. In degree zero all root powers are coefficient-unit maps;
   the same formulas apply on empty schemes and at the zero input. -/
theorem geometricPurityOrientation_exchange
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient))) :
    (P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).map
        (P.geometricPurityOrientationFactor (P.frobeniusMap f₀)
          (P.frobeniusFiber Y₀).hom d M) ≫
      (P.geometricPurityTensorSquare (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
        (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
        (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1 M).hom ≫
      ((smoothPurityTensor P.Coefficient (P.frobeniusFiber X₀).left).obj
        ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj
          (P.geometricPurityRealized (P.frobeniusFiber Y₀).left
            ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M)))).map
        (P.geometricPurityDualizingExchange (P.frobeniusMap f₀)
          (P.frobeniusFiber Y₀).hom (P.frobeniusGaloisMap X₀)
          (P.frobeniusGaloisMap Y₀)
          (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1) =
    (P.geometricPuritySource X₀ Y₀ f₀ d M).hom ≫
      P.geometricPurityOrientationFactor (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom d
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M) := by sorry

end Frobenius
end WeilConjectures.PurityFiniteSetting
