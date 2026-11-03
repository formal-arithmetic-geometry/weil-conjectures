/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons

/-! Naturality of the completed realization limit map along the datum tower transport.
Source: Stacks Tag 03DI (lemma-extension-by-zero) and Tag 091N; the final-limit paragraph.
(blueprint: lem-cbc-completed-open-exchange-transport-lemma).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Naturality of the completed realization limit map along datum tower transport.
Source: Stacks 03DI, 091N; blueprint completed exchange normalization, final-limit paragraph.
This is the transport substep used to move the forward datum comparison through
`cbcRealizationLimitMap`; the remaining strict exchange equation is
`completedOpenExchangeLimitCore`.
Proof: `cbcRealizationLimitMap (J_{j'})` is a natural transformation
`Rlim ⋙ J_{j'} ⟶ (J_{j'} on towers) ⋙ Rlim`; the displayed equation is its naturality
square at the forward tower transport `cbcDatumTowerTransport v` at `R_U K`.
(blueprint: lem-cbc-completed-open-exchange-transport-lemma). -/
theorem completedOpenExchangeTransportLemma [QuasiCompact j]
    (sq : OpenImmersionSquare v j' j g) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :
    (cbcOpenShriek d j' inferInstance).mapDerivedCategory.map
        ((completedRlim U' (U'.pbcAdicCompletion d)).map
          ((cbcDatumTowerTransport d v).hom.app
            ((completedReductionTower U d).obj K.obj))) ≫
      (cbcRealizationLimitMap (cbcOpenShriek d j' inferInstance)).app
        ((d.towerPull v).obj ((completedReductionTower U d).obj K.obj)) =
    (cbcRealizationLimitMap (cbcOpenShriek d j' inferInstance)).app
        ((completedTowerPullback v d).obj ((completedReductionTower U d).obj K.obj)) ≫
      (completedRlim T' (T'.pbcAdicCompletion d)).map
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            (cbcOpenShriek d j' inferInstance)).mapDerivedCategory.map
          ((cbcDatumTowerTransport d v).hom.app
    ((completedReductionTower U d).obj K.obj))) :=
  (cbcRealizationLimitMap (cbcOpenShriek d j' inferInstance)).naturality _

end AlgebraicGeometry.Scheme
