/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionTower
import Sheaf.Paper.SupportReductionAugmentationPull
import all Sheaf.Paper.ConstantTowerDirectImageNormalization

/-! # Proper direct image and the quotient completion unit

This is the augmentation normalization of the prescribed direct-image/limit comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

/-- The direct-image/limit comparison transports the quotient completion unit by the
actual counit-tensor projection.

Source: Stacks 099M, 099N and 0A07; proof step 4 of
lem-cbc-completed-support-intermediate-tower, the intermediate-object normalization in
the final compatibility paragraph of thm-cbc-complete-proetale.

Proof: write the quotient completion unit as the diagonal/limit unit followed by
inverse limit of the strict quotient augmentation. Naturality of directLimitIso
moves the latter map across the comparison. The constant-diagram normalization of
that comparison identifies the remaining diagonal/limit unit with the target unit
followed by inverse limit of the diagonal direct-image mate. The projection is
natural in its coefficient diagram and equals the identity at the unit coefficient:
its adjunct there is the ordinary counit. Apply this to the strict augmentation
from the constant coefficient diagram to the quotient diagram. It gives
augmentation at push(K), then projection(K), equal to the diagonal direct-image
mate followed by the tower direct image of augmentation at K. Apply inverse limit
and combine the preceding unit identity. The result is the displayed equation.
This is a calculation of actual strict diagram maps before inverse limit, and does
not infer equality from limit projections. The construction works for the zero
complex, the zero or unit ideal, and the empty scheme with the same units.
(blueprint: lem-cbc-support-proper-unit-normalization). -/
theorem supportProperUnitNormalization {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U Y : Scheme.{t}} (p : U ⟶ Y)
    (K : D (A := A) U) :
    (push (A := A) p).map ((unit d U).app K) ≫
        (directLimitIso (A := A) p).hom.app ((reduction d U).obj K) =
      (unit d Y).app ((push (A := A) p).obj K) ≫
        (rlim (A := A) Y).map (projection d p K) := by
  let a := proEtaleRingDerivedAdjunction p (exchangeConstantRing Y A)
    (exchangeConstantRing U A) (exchangeConstantIso p A)
  let b := exchangeTowerAdjunction p (exchangeConstantRing Y A)
    (exchangeConstantRing U A) (exchangeConstantIso p A)
  let ax := diagonalAdjunction (A := A) U
  let ay := diagonalAdjunction (A := A) Y
  let e := TwoSquare.mk _ _ _ _ (diagonalPullIso (A := A) p).hom
  let χ := (mateEquiv a b e).natTrans
  have hp : (mateEquiv a b
      (TwoSquare.mk _ _ _ _ (reductionPullIso d p).hom)).app K = projection d p K := by
    apply (b.homEquiv _ _).symm.injective
    change (b.homEquiv _ _).symm ((mateEquiv a b
      (TwoSquare.mk _ _ _ _ (reductionPullIso d p).hom)).app K) =
      (b.homEquiv _ _).symm ((b.homEquiv _ _)
        ((reductionPullIso d p).hom.app ((push p).obj K) ≫
          (reduction d U).map (a.counit.app K)))
    rw [Equiv.symm_apply_apply]
    exact mateEquiv_counit a b
      (TwoSquare.mk _ _ _ _ (reductionPullIso d p).hom) K
  have ht : (augmentation d Y).app ((push p).obj K) ≫ projection d p K =
      χ.app K ≫ (exchangeConstantPush (A := A) p).map ((augmentation d U).app K) := by
    rw [← hp]
    exact AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.mates_naturality a b
      (augmentation d Y) (augmentation d U) (diagonalPullIso (A := A) p).hom
      (reductionPullIso d p).hom
      (fun Z ↦ congr_app (supportReductionAugmentationPull d p) Z) K
  have hh := unit_mateEquiv ax ay (mateEquiv a b e) K
  have hl : (mateEquiv ax ay (mateEquiv a b e)).natTrans =
      (directLimitIso (A := A) p).hom := by
    exact iterated_mateEquiv_conjugateEquiv a b ay ax e
  change (push p).map (ax.unit.app K) ≫
      (mateEquiv ax ay (mateEquiv a b e)).natTrans.app ((diagonal U).obj K) =
    ay.unit.app ((push p).obj K) ≫ (rlim (A := A) Y).map (χ.app K) at hh
  rw [hl] at hh
  have hn := (directLimitIso (A := A) p).hom.naturality ((augmentation d U).app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [unit, NatTrans.comp_app, whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [hn, ← Category.assoc, hh]
  simp only [Category.assoc, ← Functor.map_comp, ← ht]
  rfl

end AlgebraicGeometry.Scheme.OrderedExchange
