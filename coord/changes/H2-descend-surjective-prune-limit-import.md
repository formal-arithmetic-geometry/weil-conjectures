# AlgebraicGeometry.exists_surjective_of_isLimit

## Reason

The proof receives the limiting cone and its universal property as hypotheses and
uses no declaration of `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
Replace that public import with `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
which supplies `IsAffineHom` used in the unchanged statement. The limit API
needed by the proof is available through its existing proof-only imports.
This removes the direct dependency on the project's limit-existence proof.
No theorem signature or definition changes; no target statement changes meaning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DescendSurjective | H2 | Only its import list changes; the theorem statement is identical. |
| Sheaf.Paper.EtaleFiniteDataDescent | unclaimed | Already imports LimitAffineTransition directly; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | unclaimed | Already imports LimitAffineTransition directly; no adaptation required. |

These are the two direct importers. The static import-pruning check found no lost
uses anywhere downstream. `tools/downstream.py --uses exists_surjective_of_isLimit`
reported no textual callers; the theorem itself is preserved in any event.

## Status

landed 20261012T060738-L-2907852 2026-10-12 (merge of deliver/H2/Sheaf.AlgebraicGeometry.DescendSurjective)
