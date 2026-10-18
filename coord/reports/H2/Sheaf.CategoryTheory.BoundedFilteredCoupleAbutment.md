## What changed

Proved `CategoryTheory.boundedFilteredComplex_coupleAbutment` in
`Sheaf.CategoryTheory.BoundedFilteredCoupleAbutment`, with its existing signature unchanged.
The proof implements all five steps of the node from the declared colimit and finite-cocone
lemmas. It constructs the colimit with the actual cohomology object and the actual inclusion
maps, and constructs the cohomology filtration by shifting the diagonal image filtration.
It verifies the finite tails, separation, exhaustiveness, inverse-limit universal property,
and the infinite-page graded-piece isomorphism.

Restored a private `finite_inverse_limit` helper using the current
`PBCDecreasingFiltration` API. Its argument is adapted from the fully proved private helper
of the same name in `WeilConjectures.CategoryTheory.HalfPlaneConvergence`; no half-plane
hypothesis or import is used. The main proof converts the shifted steps to the upstream
`DecreasingFiltration` structure without changing any definition or public interface.

The item compiled cleanly with lcompile.py (5.0 seconds). The proof is from existing declared
dependencies, as required; this does not claim those dependencies are all sorry-free.
Read Stacks `homology.tex`, label `lemma-biregular-ss-converges`, its finite-filtration
abutment and inverse-limit argument. Checked the zero-object and coincident-tail cases:
no ordering or nonzero hypothesis on the chosen whole/zero indices is used.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.boundedFilteredComplex_coupleAbutment`
(node `lem-sp-bounded-filtered-couple-abutment`).

Holes closed: 1. Holes added: 0. Split-offs: 0.
No sorry remains in the item or any delivered module. The private inverse-limit helper
is fully proved. No public declaration, definition, or statement was changed.

## No longer needed

Removed four redundant direct proof imports:
`WeilConjectures.CategoryTheory.ExactCouple`,
`WeilConjectures.CategoryTheory.ExactCoupleConvergence`,
`WeilConjectures.CategoryTheory.PBCFiltration`, and
`WeilConjectures.CategoryTheory.Abelian.Filtration`.
Their interfaces are already available through the existing public statement imports.
No mathematical dependency node or module was pruned from the import closure; all the
node's declared proof dependencies remain used. No new imports were added.

## Where the brief, the DAG or earlier work was wrong

The old commented-out inverse-limit helper took `DecreasingFiltration`, whereas the
current convergence definition requires `PBCDecreasingFiltration`. Its restored version
uses the latter, while G is built with the former's `F` and `F_succ_le` fields. The node's
proof is updated to describe this bridge and the restored helper's current name.

The generic finite-cocone convergence theorem suffices without the quotient comparison
hypothesis hγ. The original hypothesis and entire signature are preserved; a local
binding records it to keep the unused-variable linter clean. No first-quadrant hypothesis
is introduced and no unit route is bypassed. No new nodes or change records are needed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
