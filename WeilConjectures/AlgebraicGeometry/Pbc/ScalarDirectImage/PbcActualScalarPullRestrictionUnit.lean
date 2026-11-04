/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualPullProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement

/-! # The derived scalar/pullback comparison under the scalar units

The derived scalar/pullback comparison corresponds, under the scalar adjunction units, to
the canonical restriction/pullback comparison of the pro-étale ring operations.

Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y dA ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X dA ⟶ pbcAdicCompletion X dB)
    (hφ : pbcActualCoefficientRingMap Y φY ≫ pbcActualStructureMap g dB =
      pbcActualStructureMap g dA ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map (pbcActualCoefficientRingMap X φX))
    (hc : (pbcActualCoefficientIso g dA).hom ≫ φX =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map φY ≫
        (pbcActualCoefficientIso g dB).hom)

/-- The derived scalar/pullback comparison, transposed along the scalar units, is the
canonical restriction/pullback comparison.
Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: both sides are natural, so it suffices to treat flat-term K-flat complexes. There
the scalar units, the pullback counits and the scalar/pullback comparison are computed by
ordinary module maps. The ordinary comparison is the conjugate of the identity-on-sections
restriction/direct-image comparison, and the canonical restriction/pullback comparison is
the mate of the same identity-on-sections comparison; these agree on every module. -/
theorem pbcActualScalarDerivedPullIso_restriction_unit (M : PbcCompletedDerived Y dA) :
    (pbcDerivedScalarAdjunction φX).unit.app ((pbcActualDerivedPull g dA).obj M) ≫
        (pbcDerivedRestrict φX).map
          ((pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.app M) =
      (pbcActualDerivedPull g dA).map ((pbcDerivedScalarAdjunction φY).unit.app M) ≫
        (pbcActualPullProEtaleIso g dA).hom.app _ ≫
        (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.app
            ((pbcDerivedExtend φY).obj M) ≫
        (pbcDerivedRestrict φX).map ((pbcActualPullProEtaleIso g dB).inv.app _) := by
  sorry

end AlgebraicGeometry.Scheme
