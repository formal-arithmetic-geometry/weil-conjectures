## What changed

Restored `lean/Sheaf/AlgebraicGeometry/AbelianArbitrarySchemeUntensoredBaseChange.lean`
from the quarantine path recorded in `coord/rework.tsv`. The complete archived proof
and its public statement are retained. This is the assigned restoration after the
upstream synchronization and cluster quarantine, not withdrawal of the node.

The proof constructs the finitely generated subalgebra approximation and both
product-limit cones, applies finite-type abelian base change at each stage,
transfers it to bounded-below derived categories, and uses continuity in every
nonnegative degree. Exact inverse image and left exact derived direct image give
vanishing in negative degrees. The constant coefficient system includes its
identity and composition coherence.

## Proved and sorry left

`AlgebraicGeometry.Etale.abelian_affineScheme_untensored_baseChange` is restored
with its complete proof. Its node is
`lem-kun-0f1j-abelian-arbitrary-scheme-untensored-base-change`.
The archived module has zero holes; the restored module has zero holes.
Holes closed: none (0). Holes added: none (0). No split-off statements.
All private helpers and data constructions have complete bodies.

## No longer needed

None. Every archived import and all six recorded proof dependencies are retained.
The finite-type theorem, unbounded/bounded-below comparison, higher-image
continuity, affine transition theorem and finitely generated algebra colimit are
all used. The DAG attachment and unit route remain intact. In particular, the
quarantined parent `Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange`
still calls the public theorem, so its absence from current live importers is
not a reason to withdraw it.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined restoration with zero existing holes, rather than a
new proof of an unproved theorem. The archive, its Lean attachment and all its
dependencies have been preserved. Searches through leanfinder, Loogle and grep
found no shorter matching sheaf-cohomology result. The recorded argument agrees
with the affine approximation paragraph of Stacks Tag 0F1I and the higher-image
limit assertion of Tag 0EZT in the local source. No statement or definition change
is needed.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
