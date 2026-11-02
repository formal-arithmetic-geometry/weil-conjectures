/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedOpenFiniteTranspose.CompletedOpenFiniteTransposeCoherence
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare

/-! The ordinary completed-ring open mate before derived localization.
Source: Stacks Tag 03DI and the inverse-image square unit normalization.
(blueprint: lem-cbc-completed-open-ordinary-unit-mate).
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

/-- Transport the actual strict module exchange to the datum's ordinary pullbacks.
All components are specified maps; the two equality transports come from the
proved equality of the module pullback presentations.
Source: Stacks 03DI, 099N
(blueprint: lem-cbc-completed-open-ordinary-unit-mate). -/
def cbcDatumStrictInverseModule (sq : OpenImmersionSquare v j' j g) :
    d.towerModulePull v ⋙ cbcRealizationTowerJ d j' ≅
      cbcRealizationTowerJ d j ⋙ d.towerModulePull g :=
  eqToIso (congrArg (fun F ↦ F ⋙ cbcStrictOpenModule d j' inferInstance)
    (cbcDatumTowerModulePull_eq d v).symm) ≪≫
      @asIso _ _ _ _ (cbcStrictInverseModule d sq)
        (cbcStrictInverseModule_isIso d sq) ≪≫
        eqToIso (congrArg (fun G ↦ cbcStrictOpenModule d j inferInstance ⋙ G)
          (cbcDatumTowerModulePull_eq d g))

/-- The ordinary inverse exchange has the square-unit mate normalization.
Proof: first compare completedModulePullback with the datum pullback using
cbcDatumModulePull_eq. Their adjunction units agree on tensor generators by
cbcModulePullbackAdjunction_exists and the normalized ringed pullback unit.
The map cbcPullToRestriction is the transpose of the section restriction unit.
Consequently the right-adjoint mate of the inverse ringed square, transported
through cbcPullToRestriction at j and j', restricts sections along the canonical
cartesian comparison. The defining section formula and uniqueness of
cbcRightExchange identify these maps. Apply iterated mate conjugation to the
composite open/pullback adjunctions; the result is cbcUnderivedInverseExchange.
Whisker over the entire strict tower category. At every index the same ordinary
mate equation holds, and naturality gives equality of the tower transformations.
The calculation uses arbitrary sections and applies to the empty open as well.
Source: Stacks Tag 03DI, explicit extension adjunction; ringed inverse-image unit.
(blueprint: lem-cbc-completed-open-ordinary-unit-mate). -/
theorem cbcCompletedOpenOrdinaryUnitMate (sq : OpenImmersionSquare v j' j g) :
    ((mateEquiv ((cbcRealizationOpenAdj d j).whiskerRight ℕᵒᵖ)
        ((cbcRealizationOpenAdj d j').whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
            (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeModuleSquare.symm ≪≫
          (Functor.whiskeringRightObjCompIso _ _).symm).hom)).natTrans =
        (cbcDatumStrictInverseModule d sq).hom := by sorry

end AlgebraicGeometry.Scheme
