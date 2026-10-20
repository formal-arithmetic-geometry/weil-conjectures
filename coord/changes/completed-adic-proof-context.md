# Sheaf.Paper.CompletedAdicCoefficientDatum proof elaboration context

## Reason

The interface checker records module-level universe declarations and attributes,
including section-local attributes. The new private proof helpers use two fresh
universe names. The finite comparison keeps the sheaf monoidal construction
irreducible within its section, preventing unnecessary unfolding while checking
abstract derived-functor arguments. This attribute ends with that section.
Every existing public declaration has the same signature and definition body,
and every original public import is retained. No target statement or mathematical
definition changes. This record documents the context commands flagged by preflight.

## Old

```lean
universe t
```

There was no `FiniteReductionComparison` proof section or its local attribute.

## New

```lean
universe t uC vC
```

The new finite-comparison proof section opens with:

```lean
section FiniteReductionComparison

attribute [local irreducible] SheafOfModules.monoidalCategory
```

It closes with:

```lean
end FiniteReductionComparison
```

The extra universe names occur only in private helper signatures. The local
attribute is unavailable to importers. All options added before individual
proofs use `set_option ... in` and therefore affect only those proofs.

## Users

`tools/downstream.py Sheaf.Paper.CompletedAdicCoefficientDatum --direct` lists
these seven direct importers. They require no adaptation because the changed
context commands introduce no exported instance, attribute, declaration change,
or import change. The existing public-interface entries were compared with
`tools/leanindex.py`: only its `#commands` entry differs.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedAdicCoefficientDatum | E3 | proof context updated |
| Sheaf.Paper.AdicCoefficientDatum | U7 | unchanged; existing declarations and public imports are identical |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed | unchanged; existing declarations and public imports are identical |
| Sheaf.Paper.CompletedAdicIntrinsicCompletion | unclaimed | unchanged; existing declarations and public imports are identical |
| Sheaf.Paper.KoszulReconstruction | W6 | unchanged; existing declarations and public imports are identical |
| Sheaf.Paper.PbcDerivedProductRepresentation | unclaimed | unchanged; existing declarations and public imports are identical |
| Sheaf.Paper.WitnessCompatibility | X6 | unchanged; existing declarations and public imports are identical |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | unchanged; existing declarations and public imports are identical |

## Status

landed 20261020T211659-L-3487987 2026-10-20 (merge of deliver/E3/Sheaf.Paper.CompletedAdicCoefficientDatum)
