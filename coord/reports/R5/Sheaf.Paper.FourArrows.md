## What changed

Proved both original holes in `Sheaf.Paper.FourArrows` without changing any public
signature or definition. Added the proof-only import
`Sheaf.Paper.CompletedTowerDirectImage`.

For `finiteProjection_isIso`, private proved helpers identify the ordinary and
derived restriction/direct-image isomorphisms by their section and derived-unit
normalizations. An abstract adjunction mate calculation then identifies the exact
specified `finiteProjection` with `completedDirectImageProjectionFormula`.
Its existing properties theorem supplies invertibility, for arbitrary H and n.

For `finiteExchange_isIso`, constant-section uniqueness identifies the coefficient
comparisons. Equality transport over abstract ring sheaves and their isomorphisms
reduces the exact finite exchange to `finiteLevelProEtaleBaseChange` with the
original retained witness. Generalizing the rings first avoids expanding the
large coefficient presentations during kernel checking.

Updated `def-weil-pbc-four-arrows` proof steps and dependencies to this route.
Added `coord/changes/R5-four-arrows-private-proof-context.md` to document the extra
private-helper command context requested by preflight, with the consumer inventory.
All existing public signatures, definitions, visibility and public imports agree
with the current repository sources.
The full file compiled without warnings in 42.1 seconds through lcompile.py.

## Proved and sorry left

Closed both of the original 2 holes:
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteProjection_isIso`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteExchange_isIso`.

Zero holes remain in the item; zero holes added; zero split-offs. All new private
helpers are proved. The existing imported theorems retain their independent
obligations, as intended by stage 3.

## No longer needed

No existing modules or imports are removed. Existing public imports retain the
published interface; the only new import is private to the proof.

The finite projection proof reuses the already stated finite-coefficient
projection formula of `prop-weil-pbc-direct-image-limits`, rather than repeating
its perfect-coefficient argument through
`lemma-weil-pbc-perfect-projection-formula`,
`def-weil-pbc-projection-formula-map`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pc-kflat-resolution` and `lem-pur-derived-change-of-rings` directly.
These are not new direct proof dependencies of this node. Their declarations
remain needed transitively or in its existing public interface; no global pruning
of them is claimed. No blueprint unit statement or step is bypassed.
The finite exchange proof uses only the finite-level theorem, the existing
four-corners coefficient constructions, and elementary equality transport.

## Where the brief, the DAG or earlier work was wrong

The retained partial report left the projection claim open. The existing completed
direct-image module already states the needed invertibility result for the same
quotient-linear map, but in its scalar-adjunction presentation. The missing work
was identifying the normalized restriction/direct-image comparisons and proving
the mate identity. Both are now proved in Lean; no mathematical statement changed.

Earlier attempts specialized exchange before ring transport, which caused expensive
kernel comparison. Transporting abstract rings before specialization resolves it.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
