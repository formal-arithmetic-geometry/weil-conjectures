# Sheaf.RingTheory.PolynomialSquareBarNaturality imports

## Reason

Repair the returned delivery `c53793834c5`. The landing import-prune check reported:

> Sheaf.RingTheory.PolynomialSquareBarNaturality: SSet.Enhanced.trivialKanFibration
> (from Sheaf.AlgebraicTopology.TrivialKanFibration)

Removing the public import from PolynomialPresentationHomology deprives this consumer
of the alias in its public structure fields and Data definition. The requested direct import was added and the two-file packet compiled successfully,
but preflight refused that exact import as route-pivot dropped. Instead directly import
its Mathlib source and expand the alias verbatim at its three use sites. The alias is
`abbrev trivialKanFibration p := SSet.modelCategoryQuillen.I.rlp p`, so every field type
and hypothesis is definitionally identical to the original.
The current main-branch consumer is unclaimed. All declarations, proof bodies, attributes, visibility and existing imports remain
unchanged. Only the three alias occurrences (original lines 120, 220 and 221) and the
new direct Mathlib import change.

## Old

```lean
public import Sheaf.RingTheory.PolynomialPresentationHomology
public import Sheaf.RingTheory.CotangentDifferentialPresheafSes
```

## New

```lean
public import Sheaf.RingTheory.PolynomialPresentationHomology
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Sheaf.RingTheory.CotangentDifferentialPresheafSes
```

The three public field/hypothesis occurrences change as follows:

```lean
-- Old
SSet.Enhanced.trivialKanFibration
-- New (the exact body of the old abbrev)
SSet.modelCategoryQuillen.I.rlp
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PolynomialSquareBarNaturality | unclaimed | Direct Mathlib import and exact alias expansion preserve its elaborated signatures. |
| Sheaf.RingTheory.PolynomialPresentationHomology | V2 | Keeps its Mathlib replacement import and completed proof. |

No mathematical statement changes. The dropped alias module is no longer used by either delivered module. The definition
node remains needed through its existing Mathlib match. The retained consumer hole is
unchanged; no proof is weakened and no hypothesis is added or removed.

## Status

landed 20261025T005424-L-3486128 2026-10-25 (merge of deliver/V2/Sheaf.RingTheory.PolynomialPresentationHomology)
