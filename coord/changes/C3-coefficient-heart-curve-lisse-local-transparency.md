# coefficientHeart_curve_lisse_descent

## Reason

Keep actual coefficient pullback and its specified canonical comparisons abstract while
elaborating the descent proof. Local irreducibility prevents dependent types from
unfolding the full sheaf and module constructions. This is an elaboration-only command,
not a change to any definition, statement, global attribute, or public import. The
preflight conservatively requires this record for a module containing a new attribute
command. Proved private cover interfaces serve the same purpose.

## Old

No local transparency command after `coefficientHeartRefinementPullbackIso`.
All three declaration signatures and both comparison definition bodies are unchanged.

## New

```lean
attribute [local irreducible] CondensedRing.upperStar coefficientHeartFiniteFreePullbackIso
  coefficientHeartRefinementPullbackIso
```

The attribute is local to this module; importers retain the original transparency of
all three definitions. The theorem's existing signature remains verbatim and its proof
is complete. All existing public imports remain verbatim. The removed proof imports
are listed individually in report.md; all public APIs needed by the unchanged
comparison definitions remain available.

## Users

Computed with `tools/downstream.py Sheaf.Paper.CoefficientHeartCurveLisseDescent --uses`
for the theorem and for both comparison definitions. The only downstream module is
`Sheaf.Paper.SectionwiseOpenLisseHomDescent`, which uses the finite-free comparison
in two places. No consumer signature, hypothesis, conclusion, or definition changes;
therefore no target-statement semantic review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientHeartCurveLisseDescent | C3 | Local elaboration attributes and proved private helpers; theorem hole closed. |
| Sheaf.Paper.SectionwiseOpenLisseHomDescent | unclaimed | Uses the unchanged finite-free comparison; no adaptation required. |

## Status

landed 20261023T151805-L-409499 2026-10-23 (merge of deliver/C3/Sheaf.Paper.CoefficientHeartCurveLisseDescent)
