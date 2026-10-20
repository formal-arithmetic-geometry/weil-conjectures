## What changed

Retired the duplicate `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`,
which is listed in `coord/retire-items.tsv`, in favor of the already proved
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`.
The source module is untouched. Migrated the sole remaining direct importer,
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths`, by changing
one private proof import. All declarations and proof bodies in that consumer are unchanged.

Reattached `lem-sbc-stalk-normalization-normal-part` to the canonical declaration. Its
statement, proof steps, proof dependencies, and unit route are unchanged. Both DAG parents
still use the same node; no mathematics was withdrawn. No quarantine importer exists.

Change record: `coord/changes/q6-retire-stalk-normalization-normal-part.md`.

The canonical proof and its two helpers were read in full. It uses smooth ascent to
normal stalks of the source, normality of relative normalization, and the stalk ring
isomorphism of a flat preimmersion after base change. The source's finite-component
normalization theorem was also read. Empty sources have no stalks, and no connectedness
or integrality of the cover is assumed. The old signature, including the unused `let n`,
was tested by a scratch theorem proved by direct application of the canonical theorem.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both.
The migrated consumer compiles cleanly through lcompile.py.

## Proved and sorry left

This is a duplicate retirement with zero holes in the baseline item: 0 of 0 holes closed,
0 added, 0 split off, and no sorry left in any delivered Lean module. The canonical
`AlgebraicGeometry.Scheme.stalk_normalization_normal_part` is already fully proved and
has only the three permitted axioms. The compatibility check proves its unchanged
mathematical statement, including the former unused let binding.

## No longer needed

The duplicate module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`
is withdrawn. Its consumer's import is replaced by
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`.
The duplicate's two private helper copies disappear with it. No DAG node or mathematical
proof dependency is pruned: the existing node is reattached to the canonical proof,
which retains smooth normality and relative-normalization normality dependencies.

## Where the brief, the DAG or earlier work was wrong

The brief describes a repeatedly split open proof, but the current shared module already
has no sorry and the item is listed for duplicate retirement. The substantive repair is
the migration and withdrawal, not another proof or a cosmetic change to the existing one.
The earlier retirement scan kept this module because its upstream proof imports upstream
ring theory. A single-file compile of the actual migrated consumer confirms those
private proof imports cause no conflict here. The only signature text difference is the
unused `let n` omitted upstream; Lean verifies definitional equality directly.

Searches via msearch.py: LeanFinder found generic normalization construction results,
Loogle does not index the project theorem, and grep found no Mathlib theorem replacing
this result. Direct project search found the exact adopted, completely proved theorem;
that is the shortest route. No new node is needed.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
