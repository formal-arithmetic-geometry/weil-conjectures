/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenOrdinaryUnitMate

/-! Counit-normalized descent of an ordinary open mate to actual strict pullbacks.
Source: Stacks 06XN; exact localization of adjunction mates.
(blueprint: lem-cbc-completed-open-unit-mate-descent).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

/-- Exact localization carries the ordinary unit mate to the specified strict exchange.
The premise is entirely in ordinary module towers; the conclusion concerns every
object of the derived category, before quotient reduction or finite evaluation.
Proof: extend the defining normalization of cbcStrictExchange to every complex
using the levelwise K-flat covers and naturality. Compare the actual derived
pullbacks with the datum exact functors by cbcDatumTowerTransport. Cancel the
invertible exact factors after precomposition with DerivedCategory.Q. Their
counit equations identify the transported strict inverse exchange with the exact
derived image of cbcDatumStrictInverseModule. Exact localization preserves the
inverse-mate equation in the premise. Its adjunctions are precisely
cbcRealizationTowerAdj, by transport with rightDerivedFunctorIsoMapDerivedCategory.
The unit-mate identity gives the pulled unit followed by exchangeTowerSquare.inv.
Finally homEquiv naturality moves the v comparison to the source and the inverse
g comparison through the right adjoint, giving the displayed four factors.
This uses whole towers and localization, with no faithfulness claim for evaluation.
Source: Stacks 06XN; exact localization and universal pullback counits.
(blueprint: lem-cbc-completed-open-unit-mate-descent). -/
theorem cbcCompletedOpenUnitMateDescent (sq : OpenImmersionSquare v j' j g)
    (hm : ((mateEquiv ((cbcRealizationOpenAdj d j).whiskerRight ℕᵒᵖ)
        ((cbcRealizationOpenAdj d j').whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
            (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeModuleSquare.symm ≪≫
          (Functor.whiskeringRightObjCompIso _ _).symm).hom)).natTrans =
        (cbcDatumStrictInverseModule d sq).hom)
    (X : DerivedCategory (d.towers U)) :
    (cbcRealizationTowerAdj d j').homEquiv _ _ ((cbcStrictExchange d sq).inv.app X) =
      (cbcDatumTowerTransport d v).hom.app X ≫
        (d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫
        (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
          ((cbcRealizationJ d j).obj X) ≫
        (d.towerPull j').map
          ((cbcDatumTowerTransport d g).inv.app ((cbcRealizationJ d j).obj X)) := by sorry

end AlgebraicGeometry.Scheme
