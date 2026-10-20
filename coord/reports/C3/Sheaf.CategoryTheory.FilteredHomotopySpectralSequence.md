## What changed

Restored Sheaf.CategoryTheory.FilteredHomotopySpectralSequence from its quarantine
archive and migrated the retired HomPreservingSteps spelling to canonical
FilteredObject.Hom. Removed the obsolete Sheaf.CategoryTheory.Filtration import;
canonical filtration declarations come from FilteredComplexSubquotients.

Proved filteredHomotopy_page_map_eq. Lift the given homotopy to filtration steps,
then descend it through the source and target cokernels. The source step
F^(p+r) is carried into G^(p+r-1), which lies in G^(p+1) for r ≥ 2, so the
homotopy descends. Homotopy.homologyMap_eq, image-factorization cancellation and
the page model naturality equations give equality of all page maps. The three
private helpers are fully proved, and introduce no assumptions or public API.

Simplified exists_filteredHomology_map to construct the common map directly by
imageSubobjectMap on each homology square, using the supplied filtration-step
equalities. The main theorem retains its assembly of the page, abutment and
graded-map results. All three node attachments remain and their Lean records
use the current canonical Hom spelling. Updated the page and abutment proof plans.

Searches through msearch.py found no existing filtered-homotopy page theorem:
LeanFinder returned general homotopy-invariance lemmas, Loogle had no hits
(the cokernel pattern identifier was unavailable), and Mathlib grep found only
the separate homotopy-category spectral-object construction. Local library
search likewise found no direct replacement.

Single-file lcompile.py compilation succeeds without warnings. Explicit
#print axioms checks of all three public theorems show only propext,
Classical.choice and Quot.sound. The quotient argument covers r = 2, arbitrary
negative filtration indices and zero complexes; it does not require extra
boundedness. The original degreewise boundedness binders are retained, with a
local unused-variable linter setting for the page theorem.

Change record: coord/changes/filtered-homotopy-spectral-sequence-restoration.md.

## Proved and sorry left

Closed one original hole: CategoryTheory.filteredHomotopy_page_map_eq
(lem-sp-filtered-homotopy-spectral-sequence-page-map).

CategoryTheory.exists_filteredHomology_map and
CategoryTheory.filteredHomotopy_spectralSequence_map_eq remain fully proved;
the latter now has no remaining axiom from the page-map substatement.

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining: 0.
No declaration in the delivery contains sorry or depends on sorryAx.

## No longer needed

Removed import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence and
the page node's dependency thm-sp-spectral-object-yields. The supplied page model
already provides the quotient maps, image identifications and naturality, so
neither spectral-sequence construction nor its convergence proof is used here.
This is pruning of this proof's dependency; other users of that theorem remain.

Removed import Sheaf.CategoryTheory.FilteredCohomologyImage. The abutment proof
works directly with the hypotheses specifying the image steps, and needs neither
the cohomologyImage definition nor its finiteness theorem
lem-sp-filtered-cohomology-image-finite. Other users of that module remain.

Removed obsolete public import Sheaf.CategoryTheory.Filtration, which is already
an empty withdrawn module. The definition node def-sp-filtration and the actual
canonical upstream filtration remain necessary. No modules are withdrawn.
FiniteFiltrationInduction remains needed for exists_gradedMap_steps, and the
page-model and subquotient definition dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The assigned source is quarantined, rather than present under lean/. It is
restored from the exact rework.tsv archive, preserving its Lean attachments and
parent dependencies. The old duplicate filtration implementation and
HomPreservingSteps spelling are obsolete after upstream adoption.

The page node's plan used the bounded spectral-sequence construction, but that
statement does not itself express filtered homotopy invariance. Its dependency
is unnecessary: the existing page model suffices. The abutment proof's previous
identification with cohomologyImage by extensionality is likewise unnecessary.
The downstream.py --allow-missing check reports zero live importers and zero
users of all three public declarations; the archived CartanEilenberg consumer
still uses the result positionally and retains its dependency.

No target or mathematical statement changes, no new nodes, no source-library
changes, and no unit route is bypassed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
