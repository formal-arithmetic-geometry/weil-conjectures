# AlgebraicGeometry.Scheme.FiniteStageRationalExchange.HasCoherence

## Reason

Repeatedly instantiating the four expanded composite and normalization clauses
inside `HasCoherence` dominates kernel checking of the presentation construction.
Name those literal propositions, retaining every quantified variable and equation.
The existing predicate signatures, data witnesses and public imports stay identical.

The same presentation benchmark took 43.0 seconds with the original predicate and
23.6 seconds with the four named clauses. Its constructor kernel check dropped
from 26.6 seconds to 3.72 seconds. These measurements use the same proof route.

## Old

The four existing existential witness types in `HasCoherence` are:

```lean
  ∃ (_rawF_composite : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawF.β a).hom.app K)
      ((cf_rPull.β a).hom.app ((cg_rPush.Φ E).obj K) ≫
        (cf_rPull.Φ M).map ((cg_rPush.β a).hom.app K))),
  ∃ (_rawG_composite : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawG.β a).hom.app K)
      ((ch_rPush.β a).hom.app ((ce_rPull.Φ E).obj K) ≫
        (ch_rPush.Φ M).map ((ce_rPull.β a).hom.app K))),
  ∃ (_rawF_normalization : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawF.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf_pPull a).hom.app
              ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map
              ((cg_pPush a).hom.app K)) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M)
          (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))),
  ∃ (_rawG_normalization : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawG.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch_pPush a).hom.app
              ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map
              ((ce_pPull a).hom.app K)) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M)
          (h := h) (e := e)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))),
```

## New

The propositions contain the original witness types literally:

```lean
/-- The left raw composite clause, named without changing its equation.
Source: sketch32, lines 1218--1228 and 1291--1321
(blueprint: def-sbc-finite-stage-rational-exchange-data). -/
def RawLeftComposite
    (cf_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω S)
    (pbcAmbientCompleteRawSystem l Ω X))
    (cg_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω S))
    (rawF : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X))
    : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawF.β a).hom.app K)
      ((cf_rPull.β a).hom.app ((cg_rPush.Φ E).obj K) ≫
        (cf_rPull.Φ M).map ((cg_rPush.β a).hom.app K))

/-- The right raw composite clause, named without changing its equation.
Source: sketch32, lines 1218--1228 and 1291--1321
(blueprint: def-sbc-finite-stage-rational-exchange-data). -/
def RawRightComposite
    (ch_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω Y)
    (pbcAmbientCompleteRawSystem l Ω X))
    (ce_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω Y))
    (rawG : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X))
    : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawG.β a).hom.app K)
      ((ch_rPush.β a).hom.app ((ce_rPull.Φ E).obj K) ≫
        (ch_rPush.Φ M).map ((ce_rPull.β a).hom.app K))

/-- The left raw normalization clause, named without changing its equation.
Source: sketch32, lines 1218--1228 and 1291--1321
(blueprint: def-sbc-finite-stage-rational-exchange-data). -/
def RawLeftNormalization
    (cf_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) f ⋙
        pbcAmbientCompleteIntegralTransition l Ω X a ≅
      pbcAmbientCompleteIntegralTransition l Ω S a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) f)
    (cg_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) g ⋙
        pbcAmbientCompleteIntegralTransition l Ω S a ≅
      pbcAmbientCompleteIntegralTransition l Ω T a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) g)
    (rawF : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X))
    : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawF.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf_pPull a).hom.app
              ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map
              ((cg_pPush a).hom.app K)) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M)
          (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))

/-- The right raw normalization clause, named without changing its equation.
Source: sketch32, lines 1218--1228 and 1291--1321
(blueprint: def-sbc-finite-stage-rational-exchange-data). -/
def RawRightNormalization
    (ch_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) h ⋙
        pbcAmbientCompleteIntegralTransition l Ω X a ≅
      pbcAmbientCompleteIntegralTransition l Ω Y a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) h)
    (ce_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) e ⋙
        pbcAmbientCompleteIntegralTransition l Ω Y a ≅
      pbcAmbientCompleteIntegralTransition l Ω T a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) e)
    (rawG : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X))
    : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawG.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch_pPush a).hom.app
              ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map
              ((ce_pPull a).hom.app K)) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M)
          (h := h) (e := e)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))
```

`HasCoherence` now names those propositions in the same four existential binders.
Unfolding them recovers the previous predicate. No data is selected and no proof
obligation or hypothesis is removed. No theorem statement is changed.

## Users

The module and all six downstream modules were unclaimed when checked. The shared
repository is untouched; the repair and the consumer tests are in this sandbox.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteStageRationalExchangeData | unclaimed | name four existing clauses and use their names in HasCoherence |
| Sheaf.Paper.FiniteStageKaroubiExtension | unclaimed | none |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | none |
| Sheaf.Paper.RationalOperationCoherence | unclaimed | none |
| Sheaf.Paper.RationalRawOperationCoherence | unclaimed | none |
| Sheaf.Paper.RationalRawSquareExchangeCoherence | unclaimed | none |
| Sheaf.Paper.RationalSquareExchangeCoherence | unclaimed | none |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | use the same coherence witnesses in the presentation proof |

The definition module, the presentation benchmark, and all six unchanged downstream
modules compile. The seven-file consumer check completed with exit code 0. The four new declarations are
attached to the existing definition node; its mathematical statement is preserved.
This packaging is submitted for independent definition and target-meaning review.

## Status

landed 20261022T040208-L-2831428 2026-10-22 (merge of deliver/M8/Sheaf.Paper.QbarCoefficientSmoothBaseChange)
