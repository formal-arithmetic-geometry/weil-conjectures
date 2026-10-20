## What changed

Repaired the import collision in `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation`.
Preserved its theorem statement, public imports and assembly proof. Its three private proof
imports now select the fully proved original-model counterparts under
`Sheaf.AlgebraicGeometry.StrictLocalSmallModel`, with `smallModel_` helper names.
Restored the 24 proved modules from the earlier c03b8450536 landing after batch recovery
removed them. Reattached their 26 existing DAG nodes; updated the item's proof description.
No source-library file, existing mathematical statement, target or quarantine archive changes.
The localized Hom helper needed a compile-time repair: local transparency guards prevent
unnecessary unfolding of imported comparison definitions, and let bindings share repeated
terms in sourceLocalizedSectionsIso. Its data and signatures are preserved.
The change record is `coord/changes/C3-strict-local-small-model-restoration.md`.

## Proved and sorry left

Zero-hole repair: the item had 0 textual sorries and retains 0. Holes closed: 0; holes
added: 0; split off: 0. Every restored helper has 0 sorries. No unfinished proof is
repackaged or handed on. The theorem is
`AlgebraicGeometry.Etale.nonempty_strictLocalBaseChange_continuityPresentation`.
It constructs all fields of the presentation from the original-model neighbourhood
geometry, source colimit and injective-representative projection formulas.

Validation: all 25 delivery modules compile through lcompile.py within the 60-second
single-file limit. The unchanged StrictLocalBaseChangeGlobalHomology consumer also
compiles. Both its isomorphism theorem and the repaired presentation theorem report
exactly propext, Classical.choice and Quot.sound under #print axioms. All 25 modules
are transitively reached from the item, contain zero sorries and have lines of at most
100 characters. The theorem signature and public imports match the preserved quarantine
source exactly; no public statement is changed.

## No longer needed

Removed these three canonical-model private proof imports from the item:
`WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence`,
`WeilConjectures.AlgebraicGeometry.StrictLocalCohomologySourceColimit`, and
`WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionFormulas`.
Their original-model counterparts provide the needed statements. The canonical source
modules and all their proofs stay intact. No mathematical node or module is claimed
pruned. Every restored helper module is reached by the item's proof; none is unused.
The proof-dependency edges and unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

This is an assigned import/interface repair with zero textual holes. The recovered live
source selected source-library helpers which now use `Scheme.strictLocalization`, while
its statement and original Sheaf interfaces still use `Scheme.strictHenselizationScheme`.
The import collision is reproduced at `Scheme.strictHenselizationStructuralMap_eq`.
Switching only the public restriction import exposes the further mismatch between
`pullback f (strictLocalizationToBase s)` and the required original-model pullback.
A public re-export of the canonical theorem would change the assigned statement.

The earlier fully proved original-model chain is therefore restored. This follows the
DAG's existing argument rather than introducing another split. The local Stacks source
`etale-cohomology.tex`, theorem-higher-direct-images (Tag 03Q9), was checked: affine
neighbourhood limits, the cohomology colimit and injective-complex restrictions give
exactly this route. The unit `sk-prop-h2` has empty realized lists; no unit route changes.
LeanFinder found only generic cocone/limit infrastructure, Loogle found no declaration
for GlobalCohomologyContinuityPresentation, and the search service grep found no direct
match. Repository search found the proved canonical-model argument and the prior proved
original-model repair. The distinction between the two models prevents simply reusing
the canonical theorem.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
