## What changed

Added the fixed-scalar adjunction-transpose proof of
`properComponent_fixed_realization_expanded`.  The proof applies the lower
coordinate-normalization statement, then uses the counit form of the generic
right-derived lower-star projection map and injectivity of the adjunction
hom-equivalence.  Added the proof-only module
`Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization` containing the
strictly lower coordinate-normalization statement and imported it from the item.
Updated the item node's proof route and dependency list.

## Proved and sorry left

Closed one original hole:

- `WeilConjectures.CompactSupportFiniteProjection.properComponent_fixed_realization_expanded`
  (`lem-sf-finite-proper-projection-fixed-realization-expanded`).

One lower intermediate hole remains:

- `WeilConjectures.CompactSupportFiniteProjection.properComponent_fixed_realization_normalization`
  (`lem-sf-finite-proper-projection-fixed-realization-normalization`).

No other holes were added.

## No longer needed

No imports or declared proof dependencies were pruned.  The generic projection-map
counit identity is used directly from the adopted source library; all four original
statement dependencies remain needed for the item and the lower normalization
statement.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan correctly identified the expanded coordinate calculation
as a lower step, but did not record the adjunction-transpose interface needed to
combine that step with the generic projection-map identity.  The new node records
that interface explicitly without changing either existing statement.

## New nodes

`lem-sf-finite-proper-projection-fixed-realization-normalization` records the
coefficient-coordinate normalization required before the generic counit transpose.
Its declaration is in
`lean/Sheaf/Paper/FiniteProperProjectionFixedRealizationNormalization.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteProperProjectionFixedRealizationExpanded": "992d0629b04a16dc9d9f6494dc8d47bad9729290", "Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization": "63beaf647dcbb4be964a021b73c77562f83fba64"}, "results": {}, "time": "2026-10-28T06:38:26+0800", "transitive": 0, "version": 1}
```

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
