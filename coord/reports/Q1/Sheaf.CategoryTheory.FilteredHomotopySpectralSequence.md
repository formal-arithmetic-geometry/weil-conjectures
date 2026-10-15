## What changed

Updated `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` with a complete
combination proof for the target theorem. The target is decomposed into two
strict intermediate statements: equality of page maps and existence of a
common filtered cohomology map. The graded-piece conclusion is then obtained
from `FilteredObject.exists_gradedMap_steps`. Added the proof-only import
`Sheaf.CategoryTheory.FiniteFiltrationInduction` and
`Sheaf.CategoryTheory.FilteredCohomologyImage`; removed the unused bounded
spectral-sequence import.

## Proved and sorry left

The target theorem `CategoryTheory.filteredHomotopy_spectralSequence_map_eq` is
proved from the two named intermediate statements and the graded-map
construction. The only intermediate statement left as a documented `sorry` is:

- `CategoryTheory.filteredHomotopy_page_map_eq`
  (`lem-sp-filtered-homotopy-spectral-sequence-page-map`), the filtered
  homotopy calculation on every page from page two onward.

`CategoryTheory.exists_filteredHomology_map` is proved by identifying the
image filtrations, applying `Homotopy.homologyMap_eq`, and using
`imageSubobjectMap` for the step lifts.

## No longer needed

The original proof dependency `thm-sp-spectral-object-yields` and its module
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence` are no longer
imported directly by this module; their construction is isolated in the page
substatement. No other existing nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan did not expose the two independent categorical
interfaces needed by the target theorem. They are recorded as strict
substatements rather than leaving an anonymous partial proof.

## New nodes

Added `lem-sp-filtered-homotopy-spectral-sequence-page-map` and
`lem-sp-filtered-homotopy-spectral-sequence-filtered-abutment-map`, both in
`dag/nodes/sec-abelian-varieties/`. Their declarations remain in the item
module and are documented above.

## Earlier second reading (a previous round; superseded)

The top theorem's statement and signature are unchanged. The common filtered
cohomology-map substatement is strictly smaller than the target and is proved
by the image-subobject square; the page-map substatement is the only remaining
hole and retains the unit route through the bounded filtered spectral sequence.
The graded-piece conclusion uses the existing `FilteredObject.exists_gradedMap_steps`.

## Second reading by Q1

1. **Statements and signatures.** Compared the delivered module with the repository
   version. The existing target theorem keeps its signature byte for byte; the two
   added declarations are strict substatements. The target's conclusion and all
   hypotheses are unchanged.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly.
   The target and `exists_filteredHomology_map` contain no `sorry`. The sole remaining
   `sorry` is the named page-map theorem, with its matching DAG node and source
   explanation. No forbidden declarations or hollow definitions were added.
3. **New statements.** Checked that the filtered cohomology-map statement is exactly
   the image-filtration interface needed by the target and is proved by the
   image-subobject square plus `Homotopy.homologyMap_eq`. The page-map statement is
   the strict spectral-sequence calculation left open from the original plan; it is
   not a restatement of the target.
4. **Pruning and dependencies.** The target proof uses the two substatements and
   `FilteredObject.exists_gradedMap_steps`, so the DAG proof and `proof_deps` were
   updated accordingly. The direct bounded-spectral-sequence import is no longer
   needed by the declarations in this module and is removed; the page-map node still
   records that theorem as its proof dependency, preserving the unit route.
5. **Units and metadata.** The page-map and filtered-abutment nodes have matching
   Lean declarations, sources, proof steps, and chapter/unit metadata. The unit route
   through the page-map calculation remains represented in the DAG.

**Changed while reading:** corrected the root node's stale proof and dependency
   metadata to match the actual combination proof, and added this review record.
