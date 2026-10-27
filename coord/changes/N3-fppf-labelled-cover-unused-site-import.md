# AlgebraicGeometry.Scheme.fppf_labelled_cover_descent

## Reason

The complete proof uses the existing Mathlib sheaf axiom, not the auxiliary
`Precoverage.IsSiteForCoverings` definition. Remove its unused public import.
The declaration's signature is unchanged. `tools/downstream.py` reports zero
downstream modules and only the item's own declaration as a textual user.
The DAG parents remain served by the same theorem with exactly the same signature.
No target definition or target statement changes.

## Old

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
```

## New

The unused import is removed. There is no replacement definition or declaration.
The proof-only import `Mathlib.AlgebraicGeometry.Limits` supplies initiality of the
empty scheme for the coproduct proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FppfLabelledCoverDescent | N3 | Complete proof; unused public import removed; signature unchanged. |

There are zero downstream modules, hence no consumer adaptations.

## Status

landed 20261023T123914-L-1290327 2026-10-23 (merge of deliver/N3/Sheaf.AlgebraicGeometry.FppfLabelledCoverDescent)
