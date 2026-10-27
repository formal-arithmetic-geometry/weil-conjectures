## What changed

Proved `AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_associativity`
in `Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionCoherence`, using the existing
`projectionMapOfCompactification_assoc` from the private proof import
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc`.
The proof cancels the invertible forward projection factors and transports the
result through the tensor object/map APIs. Private generic helpers and a
kernel-checked heterogeneous-congruence routine avoid unfolding the concrete
derived monoidal structure. The DAG records this shorter associativity route.

All existing public signatures, public imports, the inverse definition and the
existing naturality proofs are preserved. No other module is adapted.

## Proved and sorry left

Closed one of the two starting holes:
`AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_associativity`.

The one remaining original hole is
`AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_composition`, attached to
`lem-sf-etale-compact-projection-coherence`. Its original statement and proof
plan are retained. No holes are added or split off. This is a partial delivery,
not a claim to have proved composition.

The complete delivery module compiles through `lcompile.py` in 20.9 seconds
(exit code 0), with no warnings. All five public signatures and the complete
inverse definition were compared verbatim against the live source. The added
proof import passes `tools/import_direction.py may`.

## No longer needed

No existing imports are removed; no modules or nodes are withdrawn. Removed the
item's direct proof dependency and obsolete `tool_uses` entry for
`lem-weil-pbc-site-derived-tensor-descent`. The
representative-level tensor descent and separate open/proper associativity
calculation are unnecessary for this item's associativity proof: the source
library already proves the forward associativity theorem. The DAG retains the
dependencies needed by its unfinished composition argument.

## Where the brief, the DAG or earlier work was wrong

E1 had already closed the two naturality holes, so the live item starts with two
holes. The DAG's associativity route duplicates a proved source theorem.

The exploratory graph-strength argument did not yield a complete, checked proof
of the displayed composition theorem. Its forward projection square is equivalent
to inverse composition under invertibility, so moving it to a new holed theorem
would not be a valid reduction. That square is not added to the library.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
