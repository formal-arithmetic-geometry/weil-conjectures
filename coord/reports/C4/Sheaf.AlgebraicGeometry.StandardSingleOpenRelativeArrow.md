## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleOpenRelativeArrow.lean` from its
quarantined source. The complete proof of
`AlgebraicGeometry.standardSingle_open_relative_arrow` constructs the canonical open
and pullback isomorphisms, proves invertibility of the single comparison along open
immersions, establishes the coefficient compatibility equation, and applies source
coordinate conjugacy to build the arrow isomorphism. The declaration signature and
DAG node are unchanged.

The module compiles against the current green library with `lcompile.py` without
errors or warnings.

## Proved and sorry left

The quarantined source already contains a complete proof of
`AlgebraicGeometry.standardSingle_open_relative_arrow` in node
`lem-pc-standard-single-open-relative-arrow`. Its private helper proofs are also
complete. This is a restoration repair with zero original holes: 0 holes closed,
0 added, and 0 remaining.

## No longer needed

No imports or DAG dependencies were removed. Every import in the restored module is
used by its statement or proof: the standard and relative arrow definitions, source
coordinate conjugacy, single tensor coefficient coherence, pullback pasting, derived
left-counit invertibility, and the open restriction instances.

## Where the brief, the DAG or earlier work was wrong

The module was quarantined by the rework cluster restore even though its DAG node and
previously reviewed, complete proof remained valid. Restoring the quarantined source
is sufficient; no statement, definition, downstream importer, or DAG route was
changed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
