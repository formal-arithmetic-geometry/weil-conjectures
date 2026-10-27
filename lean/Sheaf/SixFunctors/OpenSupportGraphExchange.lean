/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenRestrictionCompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import all Sheaf.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange

/-! # Cartesian exchange of the graph comparison between compactifications

Source: Stacks Project, Tag 0F7F, the product-graph base-change calculation.
(blueprint: lem-asd-open-support-graph-exchange)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] openRestrictionGraphIso sfGraphCompactificationComparison
  rightDerivedLowerShriekOfCompactificationBaseChangeMap'
  derivedOpenImmersionLowerShriekBaseChangeIso
  rightDerivedLowerShriekOfCompactificationBaseChangeMap

private theorem graph_eq_normalized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c d : Compactification f) :
    openRestrictionGraphIso Λ c d =
      etaleGraphComparisonFromOpen Λ c (EtaleGraphPresentation.ofCompactification d) ≪≫
        etaleGraphOpenNormalization Λ d := by
  simp only [openRestrictionGraphIso, etaleGraphOpenNormalization,
    ← sfComparison_eq_graphComparison, Iso.trans_assoc]
  rfl

private theorem cartesian_exchange_transport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f) (d : Compactification f')
    (w : d.Z ⟶ c.Z) (hi : IsPullback v d.i c.i w) (hp : IsPullback w d.g c.g b) :
    compactificationExactExchange Λ c d w hi hp =
      Functor.whiskerLeft Rf_!(c)[ModuleCat.{u + 1} Λ]
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) b).inv ≫
        rightDerivedLowerShriekOfCompactificationBaseChangeMap'
          (ModuleCat.{u + 1} Λ) c d w hi hp.toCommSq ≫
        Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) v).hom
          Rf_!(d)[ModuleCat.{u + 1} Λ] := by
  ext M
  have h := congr_app (exact_exchange_transport Λ hp.toCommSq)
    (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simp only [compactificationExactExchange, rightDerivedLowerShriekOfCompactificationBaseChangeMap',
    derivedOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  rw [← h]
  dsimp only [rightDerivedLowerShriekOfCompactification, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The graph factor alone commutes with Cartesian compactification exchange.
Source: Stacks Project, Tag 0F7F; `etaleGraphFromOpen_baseChange`.

Proof: apply the single-graph exchange to the presentation of d and its supplied
Cartesian representative d'. Remove R(id)_* by its unit-normalized exchange equation.
This gives the result for exact termwise inverse image. Conjugate by the canonical
isomorphisms between exact inverse image and left derived inverse image. Naturality
cancels the endpoint comparison isomorphisms. No proper exchange is inverted and no
quasi-compactness is used.
(blueprint: lem-asd-open-support-graph-exchange) -/
theorem openRestrictionGraphIso_cartesianExchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (sq : IsPullback v f' f b)
    (c d : Compactification f) (d' : Compactification f')
    (w : d'.Z ⟶ d.Z) (hi : IsPullback v d'.i d.i w)
    (hp : IsPullback w d'.g d.g b) :
    Functor.whiskerRight (openRestrictionGraphIso Λ c d).hom
        L((b)^*[ModuleCat.{u + 1} Λ]) ≫
      rightDerivedLowerShriekOfCompactificationBaseChangeMap'
        (ModuleCat.{u + 1} Λ) d d' w hi hp.toCommSq =
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c ≫
      Functor.whiskerLeft L((v)^*[ModuleCat.{u + 1} Λ])
        (openRestrictionGraphIso Λ (c.ofIsPullback sq) d').hom := by
  let A := ModuleCat.{u + 1} Λ
  have h := graphComparisonFromOpen_exchange Λ c sq
    (EtaleGraphPresentation.ofCompactification d)
    (EtaleGraphPresentation.ofCompactification d')
    (compactificationPresentationBaseChange d d' w hi hp)
  have hn := graphOpenNormalization_exchange Λ d d' w hi hp
  have hd (M : DerivedCategoryModule Λ X) :
      D((b)^*[A]).map ((openRestrictionGraphIso Λ c d).hom.app M) ≫
        (compactificationExactExchange Λ d d' w hi hp).app M =
      (compactificationExactExchange Λ c (c.ofIsPullback sq)
          (pullback.fst c.g b) (c.isPullback_i_ofIsPullback sq)
          (c.isPullback_g_ofIsPullback sq).flip).app M ≫
        (openRestrictionGraphIso Λ (c.ofIsPullback sq) d').hom.app
          (D((v)^*[A]).obj M) := by
    simp only [graph_eq_normalized, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    rw [hn M, ← Category.assoc, h M, Category.assoc]
  ext M
  have H := hd M
  rw [cartesian_exchange_transport Λ d d' w hi hp,
    compactificationExactExchange_transport Λ c sq] at H
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc] at H ⊢
  have hb := (leftDerivedUpperStarIsoMapDerivedCategory A b).inv.naturality
    ((openRestrictionGraphIso Λ c d).hom.app M)
  have hv := (openRestrictionGraphIso Λ (c.ofIsPullback sq) d').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A v).hom.app M)
  simp only [Functor.comp_obj] at hv
  rw [reassoc_of% hb, hv] at H
  apply (cancel_mono (Rf_!(d')[A].map
    ((leftDerivedUpperStarIsoMapDerivedCategory A v).hom.app M))).1
  simpa only [Category.assoc] using
    ((cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory A b).inv.app
        (Rf_!(c)[A].obj M))).1 H)

end AlgebraicGeometry.Etale
