## What changed

Reduced `WeilConjectures.SfbHomFilteredColimit.filteredColimit_comparison`
without changing its signature. The proof takes finite-free stage
quasi-isomorphisms, applies the library's proved exact-colimit stability theorem,
proves both strict cocone squares, and uses two-out-of-three to derive the
comparison quasi-isomorphism at the colimit. This last assertion is not assumed
by either new lemma.

The initial definitions and original `comparison_existsUnique` move unchanged to
a publicly reexported data module so that the two new proof modules can use them
without importing their parent. Change record:
`coord/changes/R6-internal-hom-filtered-reduction.md`.
The four-module packet compiled together, with the parent taking 37.1 seconds.

## Proved and sorry left

Original item: four holes. Closed by a complete reduction:
`WeilConjectures.SfbHomFilteredColimit.filteredColimit_comparison`.
This is a decomposition, not an independent proof or a net hole gain.

Three original holes remain:

- `WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique` (unchanged,
  moved into `DerivedInternalHomFilteredColimitData`).
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_quasiIso` (untouched).
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_restriction` (untouched).

Two new holes:

- `WeilConjectures.SfbHomFilteredColimit.internalHom_finiteFree_stage`.
- `WeilConjectures.SfbHomFilteredColimit.internalHom_filtered_continuity`.

Packet total: five named theorem holes, one old hole closed, two added.
The two strict cocone identities and the exact-colimit/two-out-of-three
combination have complete Lean proofs. Previously proved scalar existence,
scalar naturality and final derived comparison proofs are preserved.

## No longer needed

No mathematical node or module is pruned. The original unit route and plans for
the untouched holes stay. The two private proof imports from the original module
are not copied into the data module because no moved definition or statement
needs them; they remain in the original module where its existing proofs use
them. No upstream declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original final derived theorem was already proved, so changing that proof
alone would not close an assigned hole. This packet instead reduces the actual
`filteredColimit_comparison` hole. The DAG now records the two mathematical
subarguments and the unchanged representative definitions in their new modules.

Continuity must not be applied directly to the possibly unbounded K-injective
replacement. The new continuity lemma explicitly transports it through the
augmentation square and exact filtered colimits. Its plan does not impose a
lower bound on the replacement or on the Hom complex. The finite-free statement
includes rank zero and arbitrary transition matrices; finite bases are used
only for its proof, never in the maps.

## New nodes

`def-sfb-internal-hom-strict-models` attaches the unchanged tensor, Hom,
evaluation and normalization definitions to the extracted data module.

`lem-sfb-internal-hom-comparison-exists` attaches the unchanged original
existence-and-uniqueness hole to that module. This is a moved hole, not an added
mathematical assumption.

`def-sfb-internal-hom-strict-roof` attaches the unchanged uniquely normalized
comparison, denominator and continuity definitions to that module.

`lem-sfb-internal-hom-finite-free-stage` is the single finite-free basis
calculation, independent of filtered diagrams and boundedness.

`lem-sfb-internal-hom-filtered-continuity` is the colimit-side augmentation and
continuity calculation. It supplies the target cocone quasi-isomorphism and the
source tensor cocone isomorphism; the parent derives the colimit comparison.

All five nodes inherit the parent's chapter and unit. The change record is
`coord/changes/R6-internal-hom-filtered-reduction.md`.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
