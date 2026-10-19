## What changed

Implemented both bounded comparisons in `Sheaf.Paper.ConstructibleCompactnessBounded`.
The shared private proof inducts on interval width, transports the ind-constructible
cohomology across truncation isomorphisms, and applies the additive five lemma to the
coproduct ladder of five-term Hom exact sequences. Finite-support exactness and
naturality of all four squares, including connecting maps, are proved explicitly.
The chosen coproduct cofan is identified with the middle vertex cofan by its universal
property. Both public theorem signatures and the comparison definition are unchanged.

Added `Sheaf.Paper.ConstructibleSingleDegreeComparison` for the single-degree base case.
Its proof identifies concentrated objects with single homology complexes, constructs the
single-complex coproduct, shifts to degree zero, and applies `det_ind_heart_ii_sums`.
A natural additive Hom isomorphism transports that existing theorem from its canonical
Grothendieck localization to the arbitrary localization bound by the original signatures.
This new module separates the mathematical base case, not a compilation timeout.

Updated the bounded node's proof, proof dependencies and proof origin to the actual
Lean argument, and recorded the new base-case node. All additional imports are private.
Scratch probes are outside the delivered `lean/` tree.

## Proved and sorry left

Closed both original holes: `AlgebraicGeometry.ProEtale.constructible_compactness_bounded`
and `AlgebraicGeometry.ProEtale.constructible_compactness_bounded_padicAlgCl`.
Their proofs use existing declared dependencies, including the still-unproved
`AlgebraicGeometry.ProEtale.det_ind_heart_ii_sums` (node `det-ind-heart-ii-sums`).

The new `AlgebraicGeometry.ProEtale.constructible_single_degree_comparison`
(node `det-constructible-single-degree-comparison`) is also proved. No new holes are
introduced, and no `sorry` remains in either delivered module. Net textual holes closed:
two; holes added: zero. This is a proof from existing dependencies, not a decomposition.

## No longer needed

Removed `Sheaf.Paper.AmbientIndDerivedSums` / `det-ambient-ind-derived-sums`:
the induction only needs ind-constructibility at the relevant cohomology degrees of
each truncation, transported by cohomology isomorphisms. It needs no assertion that the
sum itself remains ind-constructible. The unit's bounded-width induction route is kept.

Removed `WeilConjectures.CategoryTheory.TruncationTriangle` /
`lem-weil-pbc-truncation-triangle`: the standard t-structure directly gives the required
triangle with middle object K, without a representing-complex triangle or its uniqueness
clause. Removed this obsolete entry from the node's top-level `tool_uses` list.

Removed the direct `Sheaf.Paper.DetIndHeartIISums` import from the item; its declaration
is used in the proved base-case module, so node `det-ind-heart-ii-sums` remains needed
transitively. Removed the direct `Mathlib.Algebra.Homology.Embedding.CochainComplex` and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated` imports from the item: the actual
standard t-structure and Yoneda imports provide the used APIs. The former explicit
`lem-weil-pbc-truncation-cohomology` dependency is replaced by
`def-sbc-standard-tstructure-derived-category` and its established truncation API.
No global pruning count is claimed for modules other parents may still use.

## Where the brief, the DAG or earlier work was wrong

The original plan requested ind-constructibility of the coproduct and a
representing-complex truncation triangle. The induction needs neither: it uses the
standard t-structure triangle and ind-constructibility of its two outer families.
The proof therefore removes those dependencies without changing the unit's route.

The public statements allow an arbitrary derived-category localization, whereas
`det_ind_heart_ii_sums` uses the canonical Grothendieck localization. The base case
explicitly transports the Hom comparison between these presentations by the
uniqueness equivalence of localizations. This adds no hypotheses and does not choose
arbitrary mathematical data from an unproved existence theorem. The component and
coproduct isomorphisms only transport an invariant comparison.

The retained sandbox was checked against the current source signatures. Both delivered
modules compile successfully through `lcompile.py --all`, without compiler diagnostics.
The delivery dry run additionally checks their axioms and the DAG/report records.
The first resumed preflight requested a change record for a file-level namespace
opening; the opening was removed and the proof now uses qualified triangle names,
preserving the existing file-level commands and public interface.

## New nodes

`det-constructible-single-degree-comparison` records the proved base case in
`lean/Sheaf/Paper/ConstructibleSingleDegreeComparison.lean`. It supports both coefficient
rings on locally Noetherian quasi-compact schemes and arbitrary chosen localizations.
The node records actual LeanFinder, Loogle, LeanSearch and grep queries, with no exact
existing comparison theorem found. Negative shifts, the empty family, zero sheaves,
and interval width zero are included; the strong induction only takes a predecessor
when a < b. No existing public interface is changed, so no change record or forced
consumer adaptation is needed.

The base case uses `lem-kun-grothendieck-derived-coproducts` as a generic tool: its
statement supplies the specified termwise coproduct after localization. The bounded
item continues to use the already-approved `det-def-localizing-closure-existence`
for coproducts of distinguished triangles. Neither generic input replaces a unit step.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
