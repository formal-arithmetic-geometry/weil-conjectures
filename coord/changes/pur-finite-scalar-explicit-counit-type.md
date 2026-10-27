# PurRepresentingPairFiniteScalar explicit coefficient interfaces

## Reason

The inferred counit type exposes its composite functor and realization internals. Explicit
object and counit result types express the same endpoints without unfolding those internals.
The two definitions are locally irreducible only through the declaration of `RationalPair`,
then regain normal reducibility for later coefficient and naturality definitions. Their
construction bodies do not change. A focused compile of these definitions and `RationalPair`
succeeded in 16.9 seconds.

`finiteReductionChart` now proves the projection equality by `rfl` after unfolding the
projection, avoiding the former expensive `congr 1`. It is declared before the Brown data
and elaborated with transparency respected only for this declaration. Its type and the
adjunction comparison it constructs stay unchanged; no export attribute changes.

The later coordinate declarations now respect transparency, beginning immediately before
`coordinateOrdinaryComparison`. This makes their existing local irreducibility attributes
effective during elaboration. A full-module diagnostic compile with these settings succeeded
in 41.9 seconds. No definition body or signature changes are needed for this setting.

## Old

```lean
def object (C : CoefficientData l E k) (T : CondensedERealization.Base k)
    (K : CondensedERealization.Integral l E T.scheme) :=
  (C.realization.atObject T).realization.functor.obj (ScalarLocalization.mk K)

/-- The realized counit, using the inverse of the specified compact-support comparison.
Source: blueprint rational unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def counit (C : CoefficientData l E k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L) :=
  (C.atCompactification X Y f c).realization.inv.app (ScalarLocalization.mk M) ≫
    ((C.realization.atObject Y).realization.functor.map
      ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map tau)).hom
```

```lean
def finiteReductionChart (T : Scheme.{u})
    (R : CoefficientDerivedSystemCalculus l E T) (q : ℕ) :
    (purCoefficientModel l E T).functor ⋙ R.reduction ⋙
        coefficientSequenceDerivedEvaluation l E T q ≅
      (purCoefficientModel l E T).functor ⋙
        pbcDerivedExtend
          (PurCompactSupport.projection l E (q+1) (Nat.succ_le_succ (Nat.zero_le q)) T) := by
  have e0 : coefficientFiniteDerivedExtension l E T q ≅
      pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E T q) :=
    Adjunction.leftAdjointUniq (coefficientFiniteAdjunction l E T q)
      (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E T q))
  have hp : PurCompactSupport.projection l E (q+1) (Nat.succ_le_succ (Nat.zero_le q)) T =
      completedIntegralCommRingProjectionUnrestricted l E T q := by
    simp only [PurCompactSupport.projection, eqToHom_refl, Category.comp_id]
    congr 1
  rw [hp]
  exact Functor.isoWhiskerLeft (purCoefficientModel l E T).functor
    (R.reductionEvaluation q ≪≫ e0)
```

## New

```lean
def object (C : CoefficientData l E k) (T : CondensedERealization.Base k)
    (K : CondensedERealization.Integral l E T.scheme) :
    CondensedERealization.Constructible E T.scheme :=
  (C.realization.atObject T).realization.functor.obj (ScalarLocalization.mk K)

/-- The realized counit, using the inverse of the specified compact-support comparison.
Source: blueprint rational unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def counit (C : CoefficientData l E k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L) :
    (AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.continuousCoefficientRingObj E) c).obj (object l E k C X M).obj ⟶
        (object l E k C Y L).obj :=
  (C.atCompactification X Y f c).realization.inv.app (ScalarLocalization.mk M) ≫
    ((C.realization.atObject Y).realization.functor.map
      ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map tau)).hom

attribute [local irreducible] object counit
```

After `RationalPair`, `attribute [local semireducible] object counit` restores normal unfolding.

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reduction into constant quotient coefficients, normalized by actual adjunctions.
Source: blueprint finite-extension supplement Step 3
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteReductionChart (T : Scheme.{u})
    (R : CoefficientDerivedSystemCalculus l E T) (q : ℕ) :
    (purCoefficientModel l E T).functor ⋙ R.reduction ⋙
        coefficientSequenceDerivedEvaluation l E T q ≅
      (purCoefficientModel l E T).functor ⋙
        pbcDerivedExtend
          (PurCompactSupport.projection l E (q+1) (Nat.succ_le_succ (Nat.zero_le q)) T) := by
  have e0 : coefficientFiniteDerivedExtension l E T q ≅
      pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E T q) :=
    Adjunction.leftAdjointUniq (coefficientFiniteAdjunction l E T q)
      (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E T q))
  have hp : PurCompactSupport.projection l E (q+1) (Nat.succ_le_succ (Nat.zero_le q)) T =
      completedIntegralCommRingProjectionUnrestricted l E T q := by
    simp only [PurCompactSupport.projection]
    rfl
  rw [hp]
  exact Functor.isoWhiskerLeft (purCoefficientModel l E T).functor
    (R.reductionEvaluation q ≪≫ e0)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Same objects, maps and chart; explicit endpoint types and scoped elaboration settings. |

`tools/downstream.py Sheaf.Paper.PurRepresentingPairFiniteScalar --uses object`, the same
command for `counit`, and the same command for `finiteReductionChart` each report zero
downstream modules. Only this module uses the declarations. No target signature changes.

## Status

landed 20261025T203530-L-2825074 2026-10-25 (merge of deliver/V6/Sheaf.Paper.PurRepresentingPairFiniteScalar)
