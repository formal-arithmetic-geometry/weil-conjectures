## What changed

Proved `AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunneth_leftRoute_precomp`
with its original statement in `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp`.
The proof specializes the existing `kunnethMap_symmetricFactorization`, rewrites the other
side with `kunnethMap_eq`, and cancels the final direct-image compositor.
A proved private helper identifies the two existing compositor presentations using
`conjugateEquiv_leftDerivedUpperStarComp_hom`. The coordinate comparison therefore
transports between the two Kunneth compositors exactly.

Added only private proof imports of `Sheaf.AlgebraicGeometry.EtaleKunnethSymmetricFactorization`,
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`, and
`WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric`.
Updated the item's node to describe this existing-lemma route. No other module, public
signature, definition, public import, exported instance, or exported attribute changed.
Local cached derived-category instances and local irreducibility settings keep the proof
representations small. Generic cancellation and functor-level compositor normalization avoid
expensive component-level transports; no shared definitions were changed.

Validation: the final source compiled through `lcompile.py` in 8.8 seconds with no
warnings or errors, no profiler options, and zero textual holes. The existing theorem
signature was compared verbatim with the shared source and is unchanged.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunneth_leftRoute_precomp`
(node `new-sfb-etale-coordinate-kunneth-left-route-precomp`).

Zero holes remain in the item; zero holes were added or split off.
The private helpers `compIso_hom`, `compIso_eq`, `coordinate_comp_iso`,
`coordinate_comp`, `orderedProjection_hom`, `comparison_inv`, `cancel_iso_app`, and `symmetry_inv`
are also proved.
The symmetry helper normalizes symmetry generically before coefficient specialization, avoiding
expansion of the concrete sheaf-category symmetry instances in the main proof.

## No longer needed

No existing imports were removed; all existing public imports serve the original statement.
The proof no longer needs the planned dependencies
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
(`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`) and
`lem-weil-pbc-ringed-exchange-tensor-coherence`
(`Sheaf.Paper.RingedExchangeTensorCoherence`). Their general ringed-topos interfaces
are unnecessary here because the native etale Kunneth symmetric factorization is already
proved and the native compositor compatibility is an existing source-library theorem.
These nodes remain available to their other parents; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old plan did not identify the existing proved native etale symmetric factorization.
Using it closes the obligation without another split. Its two generic ringed-topos
proof dependencies are replaced by the native Kunneth equations. The unit route and all
mathematical statements remain unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp": "245ea5a6ac27efaa22d3ac56477fda27384456a7"}, "results": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute": {"hash": "5e1041422d90c01b3c5981a9bd8d5b48207d9d4b", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T10:34:59+0800", "transitive": 0, "version": 1}
```

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
