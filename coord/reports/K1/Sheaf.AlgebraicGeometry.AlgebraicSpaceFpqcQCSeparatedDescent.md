## What changed

The item keeps its public statement and its two independent descent implications.
The proof now transports local affine-test atlases along the representing pullback
isomorphisms, proves compactness by a finite union of continuous compact images,
and applies `points_compactSpace_iff` to recover the global affine-test atlas.

Separatedness is proved directly: the absolute representable diagonal represents
relative diagonal tests; an explicit cartesian-square lemma handles diagonal base
change; Yoneda reflects the resulting scheme squares; and the given scheme fpqc
closed-immersion descent theorem finishes each test. These private helpers are proved. The server compiled the main module in 6.0 seconds
and the new module in 3.2 seconds; the final delivery also runs its compilation and
axiom checks.

The new module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcFiniteAffineTestCover`
states only the finite affine refinement and compatible-point covering construction.
It does not assume quasi-compactness of the local maps and does not assert compactness
of the resulting spaces. The item itself applies the local atlas hypotheses and
performs the compactness and atlas arguments. This is a decomposition, not a claim
that all of the original mathematics is now sorry-free.

## Proved and sorry left

Closed the item's one hole in
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_separated_of_fpqc_scheme_cover`
(node `lem-sfb-space-fpqc-qc-separated-descent`). The separatedness implication has
no new sorry dependency beyond the existing scheme descent theorem. The main theorem
has a complete Lean proof from the existing inputs and the new finite-refinement lemma.

Added one hole:
`AlgebraicGeometry.AlgebraicSpace.fpqc_finite_affine_test_cover`
(node `lem-sfb-space-fpqc-finite-affine-test-cover`). This is the only sorry left
in this delivery. One textual hole closed and one introduced: this is a decomposition, with no claim
about the ledger's measured change to the full target import closure.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` and its direct
`tool_uses` entry for `lem-trf-space-fibre-products-etale-covers`. The
finite-refinement construction still needs that node, so no
module is claimed to leave the targets' dependency closure. All of the original
geometric dependencies remain needed, directly or in the new node's proof.

The separatedness argument does not need the point-topology or quasi-compactness
arguments, or an algebraic-space model of the entire relative-diagonal target:
the explicit presheaf pullback square and the absolute representable diagonal suffice.

## Where the brief, the DAG or earlier work was wrong

The stated inputs do not expose the finite affine test construction as a Lean lemma.
The old informal steps also suppress relative-diagonal pullback compatibility and
transport along representing isomorphisms. These categorical steps are now explicit
proved helpers. The finite refinement is recorded as a genuine remaining construction.

No source, statement or definition correction was required. Empty finite coverings,
empty affine tests, identity covers, infinite original index sets and non-etale fpqc
maps are retained. In particular no flat composite atlas is asserted to be etale.
The unit and chapter route are unchanged; the new node expands the original first
step below the unit level.

## New nodes

`lem-sfb-space-fpqc-finite-affine-test-cover` records finite affine test refinements
under an arbitrary fpqc scheme family, with the representing cartesian squares and
joint point-surjectivity. Its source is the affine-test argument of Stacks 041L,
fpqc refinement and base change (022B, 022D), and compatible point lifting (03H4).
LeanSearch, LeanFinder, Mathlib/source grep, and a whole-blueprint finite-affine
search found scheme refinement lemmas but no existing statement with these
algebraic-space cartesian squares and point-cover conclusion. No change records
are needed: no existing public interface or definition is changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
