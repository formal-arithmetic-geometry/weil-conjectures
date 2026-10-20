## What changed

The queue lists this item as `retire`, not as an open proof hole.
Withdraw `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility`
and redirect the sole consumer,
`Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum`, to the adopted
`WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility`.
Only that consumer's private proof import changes; its statement and proof remain
verbatim. The adopted theorem's signature agrees byte-for-byte with the withdrawn
signature after removing the Noetherian-ring hypothesis. Thus it proves the
original statement as a specialization, with the identical canonical comparisons,
explicit local family, descent morphism, affineness and recovery conclusion.

Retain `lem-pc-fp-local-map-overlap-compatibility` and redirect only its `lean`
attachment to the source theorem, including that theorem's exact signature.
The node's statement, proof, proof dependencies and unit route stay intact.
The only DAG parent is `lem-pc-fp-local-map-datum`; it continues to use the same
node, now realized by the source theorem. No source-library file is changed.

Change record:
`coord/changes/retire-finite-presentation-local-map-overlap-compatibility.md`.

## Proved and sorry left

The assigned module has zero direct `sorry`s: proved 0 of 0; closed 0 holes;
added 0 holes; split off 0 statements. This delivery retires a duplicate rather
than claiming a proof-hole reduction.

`AlgebraicGeometry.finitePresentation_local_maps_eventually_compatible` is already
proved in the adopted source module. Its duplicate and the private `map_stage`
helper are removed with the withdrawn Sheaf module. The adapted consumer also
has zero direct holes. No declaration with `sorry` is introduced or left in any
retained delivery module. Existing transitive dependencies are not counted as
new proofs or claimed closed.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility`.
Its only importing line, in `FinitePresentationLocalMapDatum`, is replaced by the
corresponding source-module import. No mathematical node is pruned: the existing
node remains attached to the source theorem, so unfinished DAG parents retain
their dependency. In particular, the overlap-equations and recovery-transport
nodes and their modules remain needed by the source proof. The withdrawn
module's public imports are supplied by the source theorem's preserved public
imports; no consumer needs an additional import.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a `sorry` and mentions earlier splits, but
this current item is a zero-hole duplicate explicitly queued for retirement.
The source theorem already implements the plan without Noetherianity. The
DAG's old Lean attachment still selected the duplicate. Redirecting it and the
sole consumer repairs that mismatch without changing the natural-language
statement, any definition, any target, or any unit proof route.

Searches through `msearch.py`: Lean Finder returned generic quasicoherent finite
presentation results; Loogle did not know this project-specific theorem; Mathlib
grep found no match. Direct library search found the exact stronger adopted
theorem. `tools/downstream.py` and a complete Lean source search found exactly
one consumer. `import_direction.py may` confirmed the replacement import is
acyclic. The adapted consumer compiled cleanly through `lcompile.py` in 18.3 seconds.
Current claim and rework records have no conflicting consumer claim or
quarantined parent requiring adaptation.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
