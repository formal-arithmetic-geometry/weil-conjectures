/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeometricPurityFactors

/-! # Geometric base change of the tensor counit transpose

Source: current blueprint sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.md, (2); finite-geometric-purity-mate, Steps 4--6.
(blueprint: lem-pur-finite-geometric-tensor-exchange).
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
/-- Tensor counit mates commute with geometric base change. The right side uses
only the unit component of exceptional base change and the two tensor transposes.
There is no diagonal orientation, shift, primitive root or relative dimension.
Source: base-change factors (2), equivariance Steps 1--2
(blueprint: lem-pur-finite-geometric-tensor-exchange).

Proof:
1. Use the specified etale presentations of the double realizations. Comparison
   units and the realization units identify their theta maps with the original
   tensor counit transposes, by the explicit definition of smoothPurityTheta.
2. Retagging changes no underlying site, compactification or projection word.
   The canonical compact-support exchange becomes geometricPurityB after undoing
   comparison and composing the compactification refinement.
3. Naturality of the projection transformation and compact-support exchange
   identifies the two inverse-projection words. Transpose under the standing
   exceptional Hom bijection: the unit counit equation gives the ordinary
   coefficient-unit base-change map, hence geometricPurityDualizingExchange.
   The input counit equation gives geometricPurityMate, by its uniqueness.
   More explicitly, take beta to be B on etale-origin objects, so beta inverse
   is the compact-support comparison in the mate equation. Both transposes are
   inverse projection, then tensor with
   (beta inverse at omega; R of the unit counit; the pullback unit comparison),
   then the right unit constraint. This is the common transpose in
   tensorCounitExchangeCalculus_restricted, with H=f*, U=Q and V=R.
4. Both composites now transpose to inverse projection followed by the pulled-back
   coefficient-unit counit and the unit constraint. Injectivity gives equality.
   Tensor pullback and the square compositor, conjugated by the realization units,
   give exactly geometricPurityTensorSquare. The final exceptional images of the
   inverse realization units give the displayed tensor factors. All Hom tests
   are bounded below of etale origin; no ambient pro-etale adjunction is used.
   The calculation is valid for zero inputs and empty schemes. -/
theorem geometricPurityTensor_exchange
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M))
    (M₀ M₁ : Etale.DerivedCategoryModule P.Coefficient (P.frobeniusFiber Y₀).left)
    (e₀ : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      (P.frobeniusFiber Y₀).left).mapDerivedCategory.obj M₀ ≅
        P.geometricPurityRealized (P.frobeniusFiber Y₀).left M)
    (e₁ : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      (P.frobeniusFiber Y₀).left).mapDerivedCategory.obj M₁ ≅
        P.geometricPurityRealized (P.frobeniusFiber Y₀).left
          ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M)) :
    (P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).map
        (P.geometricPurityTensorFactor (P.frobeniusMap f₀)
          (P.frobeniusFiber Y₀).hom M M₀ e₀) ≫
      P.geometricPurityMate X₀ Y₀ f₀ M hM =
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
          (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1) ≫
      P.geometricPurityTensorFactor (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M) M₁ e₁ := by sorry

end Frobenius
end WeilConjectures.PurityFiniteSetting
