# SequenceKInjectiveComparison explicitly typed functors and comparisons

## Reason

The inferred types expose the full exact-localization and derived-limit construction to each
predicate that uses these comparisons. Kernel type checks of the declaration prefix alone took
about 52 seconds. Give these existing constructions explicit, definitionally equal types and use
ordinary definitions. The same prefix compiled in 38.9 seconds. No mathematical data changes.

## Old

The five declarations were abbreviations with inferred result types. The exact old functor
bodies are:

```lean
abbrev restrict := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

abbrev limitComplex :=
  Functor.mapHomologicalComplex
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) (.up ℤ)

abbrev push := coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

The old comparison definitions are also quoted verbatim below.

## New

### restrictionFactors

Old:

```lean
abbrev restrictionFactors := (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
```

New:

```lean
def restrictionFactors :
    DerivedCategory.Q ⋙ coefficientSequenceDerivedRestriction l E W ≅
      restrict l E W ⋙ DerivedCategory.Q :=
  (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
```

### limitUnit

Old:

```lean
abbrev limitUnit (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :=
  coefficientRightDerivedComparison
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) J
```

New:

```lean
def limitUnit (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    DerivedCategory.Q.obj ((limitComplex l E W).obj J) ⟶
      (coefficientConstantTowerLimit l E W).obj (DerivedCategory.Q.obj J) :=
  coefficientRightDerivedComparison
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) J
```

### restrict, limitComplex, push

The old three declarations are abbreviations with inferred types. The new declarations
have the following types and the same values:

```lean
def restrict : CochainComplex (coefficientSequenceModules l E W) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

def limitComplex : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ ⥤
    CochainComplex (scalarReductionSource l E W) ℤ :=
  Functor.mapHomologicalComplex
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) (.up ℤ)

def push : coefficientSequenceModules l E W ⥤ scalarReductionSource l E W :=
  coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

Their previous values are exactly the displayed values, with `abbrev` in place of `def`
and without the displayed result types. Explicit canonical instances `push_additive`,
`restrict_shift`, and `limitComplex_shift` expose the inherited addition and shifts.
The public-interface diagnostic with this change compiled in 27.9 seconds. The theorem
and predicate signatures keep their text and are definitionally the same types.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SequenceKInjectiveComparisonShifts | T6 | Proofs use the same constructions through explicitly typed definitions. |
| Sheaf.Paper.PurSequenceComparisonTranspose | unclaimed | Its unit parameter uses the same `push`, with the canonical additive instance. |
| Sheaf.Paper.PurSequenceDerivedNormalization | unclaimed | Uses the unchanged theorem and normalization predicates. |
| Sheaf.Paper.PurSequenceProjectionHomNormalization | unclaimed | Transitive consumer; all comparison predicates keep the same meaning. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Uses the same `push` and normalized comparison theorem. |

`tools/downstream.py --uses` finds `PurSequenceDerivedNormalization` unfolding
`restrictionFactors` explicitly in its model equality; the unchanged body preserves that proof.
No other module uses `limitUnit`.
The initial downstream scan found three importers: `PurSequenceComparisonTranspose`,
`PurSequenceDerivedNormalization`, and `PurSequenceProjectionHomNormalization`.
`PurSequenceComparisonTranspose` mentions `push` in the type of its supplied unit.
Its meaning stays identical; the explicit additive instance supplies termwise complexes. Existing target signatures and the definitions' values are unchanged;
review should confirm their explicit result types are definitionally the old inferred types.

The refreshed scan also finds `Sheaf.SixFunctors.BasicRealizationShiftSquare`; its `push`
uses concern the same canonical termwise direct image. All four consumers are checked
against the delivered interface.

## Status

landed 20261025T033956-L-192086 2026-10-25 (merge of deliver/T6/Sheaf.Paper.SequenceKInjectiveComparisonShifts)
