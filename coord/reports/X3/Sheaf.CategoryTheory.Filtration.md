## What changed

Withdraw Sheaf.CategoryTheory.Filtration, the zero-hole retire-first item, and
redirect all 11 active direct imports to
WeilConjectures.CategoryTheory.CanonicalFiltration. That official module provides
the same filtration operations and category structure. Replace the duplicate
HomPreservingSteps type by upstream FilteredObject.Hom in its consumers; the data
fields and preservation predicate agree after unfolding step.

Fifteen consumer modules are adapted. FiniteFilteredColimitComparison is retained
unchanged for recompilation only. Two helper-only modules suppress their existing
privateModule warning locally. Four existing DAG Lean attachments document the
representation migration. No upstream file, target statement, mathematical
hypothesis or unit route changes.

Change record: coord/changes/Filtration-official-api-retirement.md.

This repairs return C-36e97 at head 36e974bf1: add explicit Users entries for
Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison and
Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare. Their Scheme.IsSeparated
assumptions concern schemes, so the filtration API migration requires no source
adaptation in those modules. The refreshed scan's 95 transitive users and the
additional adapted users are all documented with current holders.

## Proved and sorry left

Assigned module: zero holes before retirement, zero after. Holes closed: none
(0 of 0). Holes added: none. Split-off results: none. This is an API retirement.
Existing complete consumer proofs stay complete. These pre-existing consumer
holes are retained verbatim:

- CategoryTheory.exists_boundedAbove_rhom_hyperExt
  (lem-per-bounded-above-rhom-hyperext): only the morphism representation changes.
- AlgebraicGeometry.Etale.cohomology_iso_sections_of_acyclic_covering_class
  (lem-kun-0bkz, UnboundedEtaleCohomologyAcyclicBasis): import migration only.
- CategoryTheory.finite_filtered_colimit_model
  (lem-weil-pbc-finite-filtered-colimit-model): import migration only.
- CategoryTheory.first_quadrant_row_collapse
  (lem-weil-pbc-first-quadrant-row-collapse): import migration only.

## No longer needed

Retire the entire Sheaf.CategoryTheory.Filtration module, including its duplicate
category instance, HomPreservingSteps structure and copied filtration operations.
Remove its imports from all 11 active direct consumers. The canonical providers
are WeilConjectures.CategoryTheory.Filtration, Abelian.Filtration and
CanonicalFiltration. No mathematical node or unit is bypassed;
def-sp-filtration remains represented by upstream DecreasingFiltration.
No additional dependency module is pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned retire-first item has no sorry. Its collision with the official
CanonicalFiltration API is recorded in coord/rework.tsv. The twin named
Filtration alone lacks the full API; CanonicalFiltration supplies the step,
antitone_step, category, induced, quotient, separatedness and gradedPiece
operations. Existing upstream FilteredObject.Hom makes HomPreservingSteps
unnecessary. The blueprint's finite/separated clause is already represented
upstream by IsFiniteSeparated, which is untouched.

The earlier Users table omitted the two modules named by C-36e97. Their textual
IsSeparated matches are Scheme.IsSeparated, unrelated to filtration
separatedness. The current source scan also found other new transitive users;
all are now listed. The earlier AdmissibleDirectImage entry is retained: its
IsSeparated occurrences concern scheme morphisms.

During the first dry run of this repair, S9 landed a complete EdgeCollapse proof
and removed its old filtration import. Preflight correctly rejected the stale
sandbox adaptation; that copy was removed. No EdgeCollapse source is delivered,
and its newly landed proof and private helpers remain intact. V3's complete
InjectiveGradedFiltrationSplits proof likewise remains intact; its only edit is
the import migration. All retained consumer files were compared with current
sources to preserve independently landed work.

Validation: lcompile.py --all compiled all 16 retained consumer modules
successfully after the current-source refresh.

The repaired packet passed deliver3.py --no-push at 7db8e1fe2e
(CODEX review class). Independent review and the global build remain pending.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
