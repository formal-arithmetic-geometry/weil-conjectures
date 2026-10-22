# Sheaf.Paper.FiniteFreeQuotientCompletion public imports

## Reason

The theorem concerns the concrete termwise scalar extension. Its proof uses
`ChangeOfRingsComplex` and `ChangeOfRingsKFlat`, without the universal derived
scalar-extension model. Remove the unused public import so this proof does not
retain that additional proof dependency. Every original declaration, signature,
and definition body is unchanged.

## Old

```lean
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
```

## New

The unused import is removed. The direct public import of
`Sheaf.Algebra.Homology.ChangeOfRingsComplex` is retained.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteFreeQuotientCompletion` reports
zero downstream modules. A direct search of both library roots also finds no
importer. Thus no consumer adaptation is required. The DAG attachment and the
statement dependencies of the item remain intact; no node or module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteFreeQuotientCompletion | S1 | Removes only the unused public import. |

## Status

landed 20261022T011928-L-3234189 2026-10-22 (merge of deliver/S1/Sheaf.Paper.FiniteFreeQuotientCompletion)
