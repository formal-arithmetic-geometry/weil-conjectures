/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralChartComparisons
public import WeilConjectures.AlgebraicGeometry.ChartDncVectorFactorData
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
import all WeilConjectures.AlgebraicGeometry.DiagonalEtaleAlphaSquare
import WeilConjectures.AlgebraicGeometry.DiagonalEtaleLocalityUnitChange
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackDerivedCoherence

/-! # Naturality of the actual diagonal source comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Steps 1--4, and parent proof Steps 4--5.
(blueprint: lem-pur-chart-diagonal-source-square).

The equation uses the published source comparison and counit-normalized dualizing
comparison for an arbitrary etale map of affine charts over the base.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  ProEtale.upperStar ProEtale.comparisonUpperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

private theorem source_square (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (w : e ≫ g = h) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    DiagonalEtaleComparison.source P d g h aY e w N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
        (P.chartDiagonalAlpha d g aY) = P.chartDiagonalAlpha d h aY ≪≫
      (omegaCongr P aY w).symm ≪≫ epsilon P g aY e N := by
  subst h
  let := P.noetherian aY
  let := P.noetherian (g ≫ aY)
  let := P.noetherian ((e ≫ g) ≫ aY)
  let := Dnc.compactifiable P g aY
  let := Dnc.compactifiable P (e ≫ g) aY
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let L := (ProEtale.upperStar
    (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor
  let E := Etale.sectionStructuralLocalityIso P.Coefficient e g (e ≫ g) rfl
  let loc := P.diagonalEtaleLocality N e g
  let ag := PurityFiniteSetting.ordinaryAlpha P d g aY
  let ah := PurityFiniteSetting.ordinaryAlpha P d (e ≫ g) aY
  let cg := P.chartDualizingUnit g
  let ch := P.chartDualizingUnit (e ≫ g)
  have ho := PurityFiniteSetting.ordinary_alpha P d g (e ≫ g) aY e rfl N
  have hu := P.diagonalEtaleLocality_unitChange N e g (e ≫ g) rfl
  have hu' : (Etale.ordinaryFinitePullback P.Coefficient e).mapIso cg ≪≫ loc =
      E ≪≫ ch := by
    simpa only [cg, ch, E, loc, chartDualizingUnit, smoothPurityUnitIso,
      OrientationCounit.unitChange, diagonalDualizingCongr, eqToIso_refl,
      Iso.trans_refl] using hu
  have hu'' : E.symm ≪≫ (Etale.ordinaryFinitePullback P.Coefficient e).mapIso cg =
      ch ≪≫ loc.symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
      Iso.symm_self_id_assoc] using
      congrArg (fun z ↦ E.symm ≪≫ z ≪≫ loc.symm) hu'
  have ho' : DiagonalEtaleComparison.sourceOrdinary P d g (e ≫ g) aY e rfl N ≪≫
      (Etale.ordinaryFinitePullback P.Coefficient e).mapIso (ag ≪≫ cg) =
      (ah ≪≫ ch) ≪≫ loc.symm := by
    rw [Functor.mapIso_trans, ← Iso.trans_assoc, ho]
    simpa only [Iso.trans_assoc] using congrArg (fun z ↦ ah ≪≫ z) hu''
  have hn := Dnc.pullComparison_naturality P e (ag ≪≫ cg)
  have hn' :
      (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst g g)
        (g ≫ aY) (pullback.diagonal g))).symm ≪≫
        L.mapIso ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso (ag ≪≫ cg)) =
      F.mapIso ((Etale.ordinaryFinitePullback P.Coefficient e).mapIso (ag ≪≫ cg)) ≪≫
        (Dnc.pullComparison P e (P.diagonalOrdinaryDualizing g)).symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
      Iso.symm_self_id_assoc, L, F, Etale.ordinaryFinitePullback, Dnc.sourceEtale] using
      congrArg (fun z ↦
        (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst g g)
          (g ≫ aY) (pullback.diagonal g))).symm ≪≫ z ≪≫
          (Dnc.pullComparison P e (P.diagonalOrdinaryDualizing g)).symm) hn
  let sg := Dnc.sourceComparison P d (pullback.fst g g) (g ≫ aY)
    (pullback.diagonal g)
  let sh := Dnc.sourceComparison P d (pullback.fst (e ≫ g) (e ≫ g))
    ((e ≫ g) ≫ aY) (pullback.diagonal (e ≫ g))
  let G := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  have ht :
      (sh ≪≫ F.mapIso
        (DiagonalEtaleComparison.sourceOrdinary P d g (e ≫ g) aY e rfl N) ≪≫
        (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst g g)
          (g ≫ aY) (pullback.diagonal g))).symm ≪≫ L.mapIso sg.symm) ≪≫
        L.mapIso (sg ≪≫ G.mapIso (ag ≪≫ cg) ≪≫
          (P.diagonalDualizingComparison g).symm) =
      sh ≪≫ F.mapIso (ah ≪≫ ch) ≪≫ F.mapIso loc.symm ≪≫
        (Dnc.pullComparison P e (P.diagonalOrdinaryDualizing g)).symm ≪≫
        L.mapIso (P.diagonalDualizingComparison g).symm := by
    rw [Functor.mapIso_trans L, Functor.mapIso_trans L]
    simp only [Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
    rw [← Iso.trans_assoc
      (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst g g)
        (g ≫ aY) (pullback.diagonal g))).symm
      (L.mapIso (G.mapIso (ag ≪≫ cg))) _, hn']
    simpa only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc] using
      congrArg (fun z ↦ sh ≪≫ F.mapIso z ≪≫
        (Dnc.pullComparison P e (P.diagonalOrdinaryDualizing g)).symm ≪≫
        L.mapIso (P.diagonalDualizingComparison g).symm) ho'
  simpa only [DiagonalEtaleComparison.source, chartDiagonalAlpha, epsilon, omegaCongr,
    omega, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Functor.mapIso_trans,
    Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc,
    sg, sh, F, G, L, ag, ah, cg, ch, loc, PurityFiniteSetting.ordinaryAlpha,
    Dnc.sourceEtale] using ht

/-- Naturality of the actual diagonal source comparison for every normalized
compact-support presentation, with the canonical pullback constraints retained.
Source: orientation-charts proof Steps 1--4, parent proof Steps 4--5
(blueprint: lem-pur-chart-diagonal-source-square).

Proof: write h = e ≫ g for the two chart projections. The ordinary alpha square of
lem-pur-diagonal-etale-alpha-square (its one-map calculation ordinary_alpha, which
factors the self-product through sourceLift and pastes the counit mates) identifies
sourceOrdinary followed by the pulled-back ordinary alpha with the ordinary alpha of h
followed by inverse structural locality. Coefficient-unit naturality
(lem-pur-diagonal-etale-locality-unit-change) replaces structural locality by
diagonalEtaleLocality after the chart dualizing units. Transport through the
ordinary-to-pro-etale comparison: naturality of pullComparison
(lem-pur-comparison-pullback-derived-coherence) moves the pulled alpha across the site
comparison, and sourceComparison and diagonalDualizingComparison cancel with their
inverses. Equality induction on e ≫ B.proj = C.proj retains the omegaCongr factor of eps.
The argument holds in dimension zero and for empty schemes; no compatibility with
coordinates or orientation is assumed. -/
theorem chart_diagonal_source_square (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    q P aV e N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (alpha P aV B) = alpha P aV C ≪≫ eps P aV e N := by
  exact source_square P d B.proj C.proj aV e.hom e.over_eq N

end WeilConjectures.PurityFiniteSetting.ChartComparisons
