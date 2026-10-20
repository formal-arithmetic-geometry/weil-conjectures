## What changed

Completed the queued retirement repair for
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually`.
Withdrew that duplicate using deleted.txt and replaced its sole direct consumer's private import
in `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually` with
`WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually`.
The consumer's theorem statement and proof are byte-for-byte unchanged.
The existing node now records the upstream theorem and its verbatim signature.

The two canonical theorem signatures differ only by the Sheaf version's unused Noetherian
instance; the upstream result is stronger and applies directly with the existing arguments.
No upstream file is edited. No target or mathematical node statement changes.
Change record: `coord/changes/retire-fp-overlap-triple-canonical-B9.md`.

## Proved and sorry left

This is a retirement repair with zero original holes. Holes closed: 0 of 0. Holes added: 0.
Sorries left in the delivered modules: none. No statements were split off.
`AlgebraicGeometry.finitePresentation_overlap_triple_canonical_eventually` is supplied by its
existing upstream proof; the duplicate declaration is withdrawn rather than counted as a new proof.
`AlgebraicGeometry.finitePresentation_overlap_triple_eventually` retains its complete proof and
now uses that upstream declaration. The adapted consumer compiled on the project server in 7.0 s.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually`.
Its duplicate private constructions and proofs (`canonicalPair`, `canonicalTriple`,
`pullback_finiteness`, `canonicalTriple_compact`, `triple_pull_iff`,
`pullback_map_zero_of_comp`, `limit_triple_defect_zero`) are retired with it.
Removed import from its sole consumer:
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually`;
replaced by the corresponding upstream proof import.

The mathematical result and node `lem-pc-fp-overlap-triple-canonical-eventually` remain needed and
are attached to upstream. Its proof dependency `lem-pc-fp-test-map-zero-eventually` remains needed
by the upstream proof. No dependency theorem, node, or other module is claimed as pruned.
The withdrawn module's five public Mathlib/source imports and two private source imports need
no local replacement: the upstream module already has the same imports.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a proof obligation, but coord/queue.tsv and
coord/retire-items.tsv identify this item as a retirement repair. Its starting file already has
zero sorries. The node still pointed to the redundant Sheaf copy; it now points to upstream,
whose theorem omits the unused Noetherian assumption. The node statement itself is preserved,
and all steps of the existing canonical-overlap argument and the unit route are preserved.
Searches through msearch.py found no more direct Mathlib replacement; the exact stronger
replacement is the existing adopted source theorem, checked against both signatures and bodies.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
