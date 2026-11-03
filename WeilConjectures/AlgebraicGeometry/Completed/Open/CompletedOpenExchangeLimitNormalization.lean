/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransportLemma
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeLimitCore
public import WeilConjectures.AlgebraicGeometry.LegacyCompletedOpenExchangeLimitCore

/-! Normalization of completed open exchange by the simultaneous strict exchange.
Source: Stacks Tags 03DI and 091N; the finite-exchange and final-limit paragraphs.
(blueprint: lem-cbc-completed-open-exchange-limit-normalization).
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

/-- The completed open exchange retains the simultaneous strict exchange normalization.
Source: Stacks Tags 03DI and 091N, completion universal property;
blueprint finite-exchange and final-limit paragraphs.
(blueprint: lem-cbc-completed-open-exchange-limit-normalization).
Proof: Represent K by a flat-term K-flat complex. The ordinary inverse exchange is
its open-unit transpose. Apply that formula at every quotient, with its transition
maps, and descend using the universal pullback counits. This is exactly the inverse
of cbcStrictExchange, transported by cbcRealizationReduction and the two counit-
normalized cbcDatumTowerTransport maps. The constant-diagram mate for extension
commutes with the strict quotient augmentation, since its transpose is compConstIso.
Consequently Rlim of this simultaneous exchange, followed by inverse open/limit,
satisfies the defining ordinary-to-completed unit equation of cbcCompletedExchange.
The complete source and target make that equation unique. Transport its equality
by cbcDatumCompletedTransport, then compose with the forward open/limit comparison.
The inverse comparisons cancel, yielding this equation. The argument uses strict
maps before localization and never tests equality by derived evaluation.
In Lean: unfold `cbcDatumCompletedExchange` and `cbcDatumCompletedTransport`, move the
forward transport at v through the limit comparison by its naturality
(`completedOpenExchangeTransportLemma`), substitute `completedOpenExchangeLimitCore`,
and combine the three strict maps by functoriality of Rlim. -/
theorem completedOpenExchangeLimitNormalization [QuasiCompact j]
    (sq : OpenImmersionSquare v j' j g)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory)
    (_hJK : cbcCompleteProperty d T r a ha
      ((cbcDerivedOpenShriek d j inferInstance).obj K.obj)) :
    (cbcDatumCompletedExchange d sq r a ha).app K ≫
        (cbcRealizationLimitMap (cbcOpenShriek d j' inferInstance)).app
          ((d.towerPull v).obj ((completedReductionTower U d).obj K.obj)) =
      (completedRlim T' (d.completedRing T')).map
        ((cbcDatumTowerTransport d g).inv.app
            ((completedReductionTower T d).obj
              ((cbcDerivedOpenShriek d j inferInstance).obj K.obj)) ≫
          ((completedTowerPullback g d).map (cbcRealizationReduction d j K.obj).hom ≫
            (cbcReductionStrictExchange d sq).hom.app K.obj) ≫
          (cbcRealizationJ d j').map
            ((cbcDatumTowerTransport d v).hom.app
              ((completedReductionTower U d).obj K.obj))) := by
  have hn := completedOpenExchangeTransportLemma d sq r a ha K
  dsimp only [cbcDatumCompletedExchange, cbcDatumCompletedTransport,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  simp only [Category.assoc]
  erw [hn]
  erw [reassoc_of% (completedOpenExchangeLimitCore_legacy d sq r a ha K)]
  dsimp only [ObjectProperty.ι_obj]
  change (completedRlim T' (d.completedRing T')).map _ ≫ _ = _
  rw [← Functor.map_comp]
  simp only [Functor.map_comp, cbcRealizationJ, cbcRealizationTowerJ]
  simp only [Category.assoc]
  congr 1

end AlgebraicGeometry.Scheme
