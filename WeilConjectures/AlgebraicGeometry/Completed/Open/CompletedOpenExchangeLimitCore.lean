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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary

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

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The open factor in integral compact-support base change is the localization of
its specified degreewise exchange, in both directions, over coefficients `p_X^* Λ`.
The complex comparison here is constructed from the canonical inverse open-unit mate;
it is not chosen from an existence statement.

Source: latest blueprint `thm-cbc-complete-proetale`, proof, second arrow,
and `det-def-sfb-open-base-change`; the unbounded representative computation is
`lem-sp-condensed-open-base-change-arbitrary`.
Proof: use the existing representative theorem for the specified condensed open
base-change isomorphism. Its complex comparison has the same hom component as the
explicit degreewise comparison in every degree. Extensionality of complex morphisms
and then of isomorphisms identifies the two comparisons. Substitute this equality in
both localization equations. The derived exchange is a natural isomorphism, so its
components are invertible. This applies also to
zero complexes, identity base change, and empty open subschemes. No completeness or
product-preservation assumption is needed in the current blueprint route.
(blueprint: lem-cbc-completed-open-exchange-limit-core). -/
theorem completedOpenExchangeLimitCore
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U Z Z' : AlgebraicGeometry.Scheme.{u}}
    (j : U ⟶ Z) [AlgebraicGeometry.IsOpenImmersion j] (a : Z' ⟶ Z)
    (K : CochainComplex (condensedModuleCategory U Λ) ℤ) :
    let L := ((upperStar Λ.X a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((openImmersionLowerShriek Λ.X j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
    let R := ((openImmersionLowerShriek Λ.X (pullback.snd j a)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((upperStar Λ.X (pullback.fst j a)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
    let c : L ≅ R := HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (condensedOpenBaseChangeIso Λ j a).app (K.X n))
      (fun i k _ ↦ ((condensedOpenBaseChangeIso Λ j a).hom.naturality (K.d i k)).symm)
    IsIso ((condensedOpenBaseChangeDerivedIso Λ j a).hom.app (DerivedCategory.Q.obj K)) ∧
      (condensedOpenBaseChangeDerivedIso Λ j a).hom.app (DerivedCategory.Q.obj K) ≫
          (openImmersionLowerShriek Λ.X (pullback.snd j a)).mapDerivedCategory.map
            ((upperStar Λ.X (pullback.fst j a)).mapDerivedCategoryFactors.hom.app K) ≫
          (openImmersionLowerShriek Λ.X (pullback.snd j a)).mapDerivedCategoryFactors.hom.app
            (((upperStar Λ.X (pullback.fst j a)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) =
        (upperStar Λ.X a).mapDerivedCategory.map
            ((openImmersionLowerShriek Λ.X j).mapDerivedCategoryFactors.hom.app K) ≫
          (upperStar Λ.X a).mapDerivedCategoryFactors.hom.app
            (((openImmersionLowerShriek Λ.X j).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫ DerivedCategory.Q.map c.hom ∧
      (condensedOpenBaseChangeDerivedIso Λ j a).inv.app (DerivedCategory.Q.obj K) ≫
          (upperStar Λ.X a).mapDerivedCategory.map
            ((openImmersionLowerShriek Λ.X j).mapDerivedCategoryFactors.hom.app K) ≫
          (upperStar Λ.X a).mapDerivedCategoryFactors.hom.app
            (((openImmersionLowerShriek Λ.X j).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) =
        (openImmersionLowerShriek Λ.X (pullback.snd j a)).mapDerivedCategory.map
            ((upperStar Λ.X (pullback.fst j a)).mapDerivedCategoryFactors.hom.app K) ≫
          (openImmersionLowerShriek Λ.X (pullback.snd j a)).mapDerivedCategoryFactors.hom.app
            (((upperStar Λ.X (pullback.fst j a)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫ DerivedCategory.Q.map c.inv := by
  intro L R c
  obtain ⟨c', hc', _, hf, hi⟩ := condensed_open_base_change_arbitrary Λ j a K
  have hcc : c' = c := by
    apply Iso.ext
    ext n
    exact hc' n
  subst c'
  exact ⟨inferInstance, hf, hi⟩

end AlgebraicGeometry.ProEtale.CondensedRing
