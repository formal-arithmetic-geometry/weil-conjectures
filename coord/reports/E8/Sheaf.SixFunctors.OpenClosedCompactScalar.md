## What changed

Proved `AlgebraicGeometry.Etale.openClosedCompactScalar_coherence` with its signature
unchanged. The open and proper normalization isomorphisms are actual composites of
compactification comparisons and the canonical identity functor comparisons.
Their scalar equations follow from the proved identity normalizations and refinement
coherence. A generic, proved naturality calculation transports the scalar composition
square along each normalization. The equality of structural maps then pastes the open
factorization with the inverse closed factorization.

Added only private proved helpers and proof imports in the item module. Reused the
proved bounded-constructible, exact-flat-functor and finite scalar flat-model helpers
from `Sheaf.Paper.CoefficientDualizingOpenTensor`. Updated the item's DAG proof and
dependencies to describe the implemented argument. No other existing module changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.openClosedCompactScalar_coherence`
(node `open-closed-compact-scalar-coherence`).

Holes closed: 1. Holes added: 0. Holes remaining in the item: 0. No split-off theorem.
All private helper theorems are proved; all private definitions are explicit composites.
The item compiled cleanly through lcompile.py in 15.6 seconds, with no warnings.
Its original signature and declaration docstring are unchanged.

## No longer needed

Removed planned proof dependency `lem-pur-etale-open-derived-tensor`
(`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`):
no tensor projection formula is required for this scalar square. Boundedness is supplied
by the existing exact-flat and scalar flat-model calculations. This module may still be
needed elsewhere; no upstream declaration or module is withdrawn.

No original import was removed: the three public imports are still required by the
unchanged theorem statement. Added proof imports are used for their existing lemmas.

## Where the brief, the DAG or earlier work was wrong

The planned open-derived-tensor dependency does not itself state preservation of a
constructible Tor interval. The proof instead reuses the already proved interval and
bounded-constructibility calculations in `CoefficientDualizingOpenTensor`.
The remaining plan is implemented directly. No new intermediate obligation or altered
statement was needed. Identity and empty-open cases are covered by the same canonical
identity normalizations and categorical cancellation; no nonemptiness hypothesis occurs.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenClosedCompactScalar": "67b81466aa117c7e27bdee9b172258de5383f538"}, "results": {"Sheaf.SixFunctors.ClosedOpenDualizingMate": {"hash": "5d4e465f5c9d2de0af3f530e24f31304bf81d7dc", "status": "OK"}}, "seconds": 89, "time": "2026-10-28T14:21:13+0800", "transitive": 0, "version": 1}
```

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
