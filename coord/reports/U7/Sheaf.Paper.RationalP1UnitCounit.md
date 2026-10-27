## What changed

Restored `lean/Sheaf/Paper/RationalP1UnitCounit.lean` from its current rework archive,
including every public declaration and the uniquely normalized unit/counit construction.
Repaired the assigned heartbeat failure in `unitCounit_exact` by sharing the two
canonical additive-shift instance families through proof-valued local lets before
elaborating exactness. The proposition is definitionally unchanged after reducing
the lets and using proof irrelevance. Removed the two inherited settings that disabled
respect for transparency. No heartbeat or file-time limit was increased. The final module compiles cleanly
through `lcompile.py` in 11.7 seconds at the unchanged default heartbeat limit
for the repaired exactness declaration.

The change record is `coord/changes/U7-rational-p1-exactness-elaboration.md`.
The existing node's Lean attachment is retained, with its obsolete withdrawal note
updated to describe restoration. Its mathematical statement and proof route stay intact.

## Proved and sorry left

This is an assigned quarantine/build repair, not a proof or decomposition.
Holes closed: 0 of the 5 archived holes. Holes added: 0. Split-off statements: 0.
The following five existing theorem holes remain, all under
`det-prop-p1-adjunction-rational-unit-counit` in namespace
`AlgebraicGeometry.ProEtale.RationalP1`:

- `localizingPreservation`
- `unitInversions`
- `counitInversion`
- `unitCounit_existsUnique`
- `unitCounit_exact`

All holes retain their existing named theorem, source and complete prose proof.
No sorry appears inside a definition. `unitCounit` still chooses only from the
normalization theorem that uniquely determines the pair of natural transformations.

## No longer needed

None. No imports, declarations, nodes or modules are pruned. Both quarantined parent
modules and the unit route remain needed. The archive itself is preserved.

## Where the brief, the DAG or earlier work was wrong

The current rework record correctly identifies an elaboration failure at the first
triangulated-functor assertion. Diagnostic compilation reproduces the timeout and
shows repeated inference of additive-shift families as the expensive operation.
Supplying those same canonical proof families explicitly avoids that inference work.
The DAG's Lean note describing a withdrawn module was stale; restoration preserves
its existing attachment and all dependencies. The construction and its mathematical
proof plan are unchanged.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
