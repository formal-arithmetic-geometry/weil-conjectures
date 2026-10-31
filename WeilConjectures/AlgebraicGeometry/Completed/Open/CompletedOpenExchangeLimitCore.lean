/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedStrictOpenExchange

/-! The canonical completed open exchange is Rlim of the simultaneous strict exchange.
Source: Stacks Tags 03DI and 091N; the finite-exchange and final-limit paragraphs.
(blueprint: lem-cbc-completed-open-exchange-limit-core).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

/-- Strict quotient/open exchange after derived inverse limit: the canonical completed
exchange `cbcCompletedExchange`, followed by the open/limit comparison of `j'_!`, is
Rlim of the reduction comparison for `j_!` pulled back along `g` followed by the
simultaneous strict exchange.
Source: Stacks 03DI (lemma-extension-by-zero), 091N (derived-completion universal property);
blueprint: lem-cbc-completed-open-exchange-limit-normalization, finite-exchange and
final-limit paragraphs.
Proof: Represent K by a flat-term K-flat complex. The ordinary inverse exchange is its
open-unit transpose; applied at every strict quotient, with its transition maps, it is
the simultaneous strict exchange `cbcReductionStrictExchange`. The constant-diagram mate
`cbcRealizationLimitMap` commutes with the strict quotient augmentations, since its
transpose is `compConstIso`; for quasi-compact `j'` it is invertible because extension
by zero preserves countable products. Hence Rlim of the reduction exchange followed by
the inverse open/limit comparison satisfies the ordinary-to-completed unit equation
defining `cbcCompletedExchange` (`cbcCompletedExchange_exists`). Source and target are
complete, so that equation determines the map; composing with the forward open/limit
comparison gives the displayed equation.
(blueprint: lem-cbc-completed-open-exchange-limit-core). -/
theorem completedOpenExchangeLimitCore [QuasiCompact j]
    (sq : OpenImmersionSquare v j' j g) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :
    (cbcCompletedExchange d sq r a ha).app K ≫
        (cbcRealizationLimitMap (cbcOpenShriek d j' inferInstance)).app
          ((completedTowerPullback v d).obj ((completedReductionTower U d).obj K.obj)) =
      (completedRlim T' (d.completedRing T')).map
        ((completedTowerPullback g d).map (cbcRealizationReduction d j K.obj).hom ≫
          (cbcReductionStrictExchange d sq).hom.app K.obj) := by
  sorry

end AlgebraicGeometry.Scheme
