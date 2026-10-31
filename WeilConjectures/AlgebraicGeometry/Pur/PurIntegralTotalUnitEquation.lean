/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralTower.PurStrictIntegralExchangeData

/-! # The total compact-support completion-unit square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The specified proper and open completion-unit squares paste to the total square.

Source: the constituent compatibility paragraph of the blueprint proof of
prop-pur-weil-equivariance-compatibilities, original strict integral normalization
step 9 (blueprint: lem-pur-integral-total-unit-equation).

Proof: expand completedCompactSupportExchange into completedExchange followed by
proper direct image of cbcDatumCompletedExchange. The completedExchange_unit law
moves the source completion unit past the proper factor. Functoriality of the
proper direct image combines the input completion unit with the completed open
factor. Apply cbcDatumCompletedExchange_unit and replace its ordinary exchange
by the assumed beta identification. Split the resulting direct-image composite.
The ordered ordinary proper factor and direct image of beta are exactly the
component of purIntegralReindexingExchange; the final direct image of the open
extension of the input unit is cbcSupport.map of that unit. Associativity gives
the displayed equality. No cancellation, invertibility, origin witness, or finite
evaluation faithfulness is used. Empty schemes, zero objects and empty generating
tuples obey the same categorical identities. This is only the final total square;
it asserts none of the strict proper identities or the input units' invertibility. -/
theorem purIntegralTotalUnitEquation
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (hbeta : (cbcDatumOrdinaryExchange d sj).app K.obj =
      (cbcBeta d g' c'.i c.i gb sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst
          sj.hom_snd)).hom.app K.obj) :
    d.ordinaryToCompleted g ((cbcSupport d c).obj K.obj) ≫
        completedCompactSupportExchange d c c' gb sp sj r a ha K =
      (purIntegralReindexingExchange d c c' gb sp sj).app K.obj ≫
        (cbcSupport d c').map (d.ordinaryToCompleted g' K.obj) := by sorry

end AlgebraicGeometry.Scheme
