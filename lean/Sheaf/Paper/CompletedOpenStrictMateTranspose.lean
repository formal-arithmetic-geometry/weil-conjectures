/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Sheaf.Paper.CompletedOpenFiniteTransposeCoherence
public import Sheaf.Paper.CompletedRingStrictFiniteExchange

/-! The strict normalized exchange is the transpose of the pulled open unit.
Source: Stacks Project, Tag 03DI; blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-strict-mate-transpose).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

/-- The normalized strict inverse exchange has the specified open-unit transpose.
Proof: the section formula for cbcRightExchange restricts to the same common
fiber product. Under the explicit extension-presheaf adjunction, its conjugate
is extension of pullback of the open unit, followed by the inverse square
compositor and the open counit. Apply this section equation simultaneously at
every tower index and cochain degree; naturality commutes with all quotient
transitions and differentials. The representative equation in
CbcStrictExchangeNormalization and uniqueness of left-derived descent identify
this strict inverse mate with cbcStrictExchange.inv. Transport at v and g by the
counit-normalized cbcDatumTowerTransport. Finally adjunction naturality moves the
inverse quotient/open comparison through the right adjoint. Its adjunction input
is the reduced open unit by the definition of cbcRealizationReductionInv. The
resulting four factors are precisely unitArrow. This applies also to the empty
open and the zero object, since the section equation uses the actual zero
extension summands and never cancels a section.
Source: Stacks Tag 03DI and the finite-exchange normalization paragraph.
(blueprint: lem-cbc-completed-open-strict-mate-transpose). -/
theorem completedOpenStrictMateTranspose (sq : OpenImmersionSquare v j' j g)
    (K : d.derived U) :
    ((cbcRealizationTowerAdj d j').homEquiv _ _)
        ((completedTowerPullback g d).mapIso (cbcRealizationReduction d j K) ≪≫
          (cbcReductionStrictExchange d sq).app K).inv =
      CompletedOpenFiniteTranspose.unitArrow d sq K := by
  sorry

end AlgebraicGeometry.Scheme
