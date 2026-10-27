/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.PurStrictIntegralExchangeData
import all Sheaf.Paper.StrictTowerExchangeMateNormalization
import Sheaf.Paper.CompletedExchangeUnit
import Sheaf.Paper.PurIntegralGeometricInputNormalization
import Sheaf.Paper.PurIntegralStrictCalculus
import Sheaf.Paper.PurIntegralStrictReduction
import Sheaf.Paper.PurIntegralCompletedCoherence
import Sheaf.Paper.PurIntegralTotalUnitEquation

/-! # Strict integral exchange normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
private theorem reindexingProperNormalization
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) (M : d.derived X)
    (hsource : IsIso (d.ordinaryToCompleted g ((d.push p).obj M)))
    (hinput : IsIso (d.ordinaryToCompleted v M)) :
    PurIntegralProperNormalization d sq M := by
  have hv : d.towerV' sq M = (purReindexingRingedSquare d sq).exchangeTowerMate.app
      ((completedReductionTower X d).obj M) := completedExchange_mate d sq M
  refine ⟨?_, hv, hsource, hinput, d.completedExchange_unit sq M⟩
  rw [← hv]
  have hexp : d.towerV' sq M =
      (exchangeRealizationH (f := p) (g := g) d M).inv ≫
        (completedReductionTower Y' d).map ((d.integralExchange sq).app M) ≫
        (exchangeRealizationHPrime (f' := p') (g' := v) d M).hom := by
    simp only [AdicCoefficientDatum.towerV', AdicCoefficientDatum.towerH,
      AdicCoefficientDatum.towerV, AdicCoefficientDatum.towerH',
      exchangeRealizationH, exchangeRealizationHPrime, Iso.trans_inv, Iso.trans_hom,
      Iso.app_inv, Iso.symm_inv, Category.assoc]
  rw [hexp]
  simp only [Iso.hom_inv_id_assoc]
  rfl


attribute [local irreducible] cbcDerivedOpenShriek cbcDatumCompletedExchange
  cbcDatumOrdinaryExchange cbcBeta
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem reindexingSupportNormalization
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (hsource : IsIso (d.ordinaryToCompleted g ((cbcSupport d c).obj K.obj)))
    (hopen : IsIso (d.ordinaryToCompleted gb ((cbcJ d c.i).obj K.obj)))
    (hinput : IsIso (d.ordinaryToCompleted g' K.obj))
    (hbeta : (cbcDatumOrdinaryExchange d sj).app K.obj =
      (cbcBeta d g' c'.i c.i gb sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst
          sj.hom_snd)).hom.app K.obj) :
    PurIntegralSupportNormalization d c c' gb sp sj r a ha K := by
  let M := (cbcJ d c.i).obj K.obj
  let beta := cbcBeta d g' c'.i c.i gb sj.w
    (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)
  have hproper : PurIntegralProperNormalization d sp M :=
    reindexingProperNormalization d sp M hsource hopen
  have hqc : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hopenUnit : d.ordinaryToCompleted gb M ≫
      cbcRealizationOpenFactor d c c' gb sj r a ha K =
        beta.hom.app K.obj ≫ (cbcJ d c'.i).map (d.ordinaryToCompleted g' K.obj) := by
    exact (cbcDatumCompletedExchange_unit d sj r a ha K).trans
      (congrArg (fun e ↦ e ≫ (cbcJ d c'.i).map (d.ordinaryToCompleted g' K.obj)) hbeta)
  refine ⟨hproper, hinput, hbeta, hopenUnit, ?_⟩
  exact purIntegralTotalUnitEquation d c c' gb sp sj r a ha K hbeta




attribute [local irreducible] pbcIntegralDatum
attribute [local irreducible] PurIntegralStrictMapNormalization PurIntegralStrictHorizontal
  PurIntegralStrictVertical PurIntegralStrictReduction PurIntegralCompletedCoherence
  PurIntegralSupportNormalization

/-- The integral exchange agrees with the unit-normalized reindexing maps before
reconstruction, after reconstruction with the specified limit comparisons, and
under strict identity, horizontal, vertical and integral reduction operations.

Source: constituent-compatibility paragraph of the blueprint proof of
prop-pur-weil-equivariance-compatibilities, extracted semilinear-exchange steps 12--14
(blueprint: lem-pur-isomorphism-strict-integral-exchange-normalization).

Proof plan, following the fifteen DAG steps:
1. Use purCompletedReductionReindexing for exact completed-ring and tower
   reindexing, with profinite coefficient projections and transitions retained.
2. On flat-term K-flat representatives the two tensor comparisons relabel the
   same pure tensor, also for every quotient transition, on the diagram site.
3. Transpose r H and R(e) H prime under the tower pullback/direct-image
   adjunction. ProjectionMateExact identifies their transposes with the two
   sides of the ambient mate's defining counit equation. Ringed exchange/tensor
   coherence proves equality as strict-tower maps, without evaluation faithfulness.
4. Compose with the inverse of the specified H to obtain v = r on strict towers.
5. DirectImageLimits identifies both reconstruction units with precisely its
   direct-image/Rlim comparison, and H, H prime with their specified limit maps.
6. Substitute in completedExchange and use functoriality of Rlim. Naturality of
   the quotient completion unit identifies the reconstructed proper factor with r_M.
7. OpenTensorNormalization fixes beta inverse as the transpose of the pulled
   open unit. RingedOpenStrictReduction fixes its strict quotient tensor formula.
8. CompletedOpenStrictMateIdentification and RingedOpenScalarLimitCoherence
   preserve that unit through scalar restriction and limits. Complete endpoints
   allow cancellation of the specified quotient units, yielding the ordinary beta.
9. Substitute these two factors in completedCompactSupportExchange. All arrows
   are natural in K, hence the equality is one of natural transformations.
10. Identity and successive relabelings agree on the diagram sites; mate pasting
    and open-unit transposition give the strict horizontal equations.
11. On compatible towers the clopen identity/zero projections defining alpha
    commute with reindexing and reduction. Their proper mates therefore commute.
12. Apply the strict proper/open calculus to obtain vertical interchange before
    Rlim, retaining the finite-etale-origin domain when inverting composition maps.
13. Quotient transitions and coefficient comparisons preserve these actual
    strict maps. Evaluation yields their specified finite reduction squares.
14. Flat scalar restriction identifies the ringed D with the constant-ring D
    on the retained etale-origin domain. Its conservativity reflects invertibility;
    no faithfulness on arbitrary derived morphisms is used for the equality.
15. Apply functorial Rlim and the canonical open/limit and direct-image/limit
    comparisons. Their unit normalization gives the same completed equations.
-/
theorem purStrictIntegralExchangeNormalization (P : WeilConjectures.PurityFiniteSetting.{t}) :
    PurStrictIntegralGeometricNormalization P ∧
    PurIntegralStrictMapNormalization (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurIntegralStrictHorizontal (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurIntegralStrictVertical (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurIntegralStrictReduction (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurIntegralCompletedCoherence (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) := by
  obtain ⟨hmap, hhorizontal, hvertical⟩ := purIntegralStrictCalculus P
  refine ⟨?_, hmap, hhorizontal, hvertical, purIntegralStrictReduction P,
    purIntegralCompletedCoherence P⟩
  intro X' X Y' Y _ _ _ _ _ _ _ _ f _ _ _ _ f' g g' _ _ c c' gb _ sp sj r a ha K
  let d := pbcIntegralDatum P.coefficients.l P.extension
  obtain ⟨hsource, hopen, hinput, hbeta⟩ :=
    purIntegralGeometricInputNormalization P c c' gb sp sj r a ha K
  exact reindexingSupportNormalization d c c' gb sp sj r a ha K hsource hopen hinput hbeta

end AlgebraicGeometry.Scheme
