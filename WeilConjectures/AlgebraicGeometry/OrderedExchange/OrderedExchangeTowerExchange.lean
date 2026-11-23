/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData

/-! # The constant ambient exchange and the strict projection

The ambient exchange `constantExchange` with constant coefficients, and the naturality of the
strict projection in the ambient input (`projection_naturality`).

## References

* Stacks 07A7, 0D6D, 0E48
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The ambient exchange with constant coefficients. -/
abbrev constantExchange (sq : ChosenCartesianSquare g' f' f g) :
    push (A := A) f ⋙ pull (A := A) g ⟶ pull (A := A) g' ⋙ push (A := A) f' :=
  proEtaleAmbientRingedExchange sq (exchangeConstantRing X A) (exchangeConstantRing Y A)
    (exchangeConstantRing X' A) (exchangeConstantRing Y' A) (exchangeConstantIso f A)
    (exchangeConstantIso g A) (exchangeConstantIso g' A) (exchangeConstantIso f' A)
    (exchangeConstant_coherent sq)

/-- The strict projection is natural in the ambient input. -/
theorem projection_naturality {U V : Scheme.{t}} (u : U ⟶ V) {M N : D (A := A) U}
    (a : M ⟶ N) :
    (reduction d V).map ((push (A := A) u).map a) ≫ projection d u N =
      projection d u M ≫ (exchangeConstantPush (A := A) u).map ((reduction d U).map a) := by
  let aj := exchangeTowerAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  let ar := proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  let pi0 := (mateEquiv ar aj (TwoSquare.mk _ _ _ _ (reductionPullIso d u).hom))
  have hpi (M : D (A := A) U) : pi0.app M = projection d u M := by
    apply (aj.homEquiv _ _).symm.injective
    change (aj.homEquiv _ _).symm (pi0.app M) =
      (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
        ((reductionPullIso d u).hom.app ((push (A := A) u).obj M) ≫
          (reduction d U).map (ar.counit.app M)))
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact mateEquiv_counit ar aj (TwoSquare.mk _ _ _ _ (reductionPullIso d u).hom) M
  rw [← hpi, ← hpi]
  exact pi0.naturality a

end AlgebraicGeometry.Scheme.OrderedExchange
