## What changed

Completed both coefficient-case theorems in `Sheaf.Paper.ProperUnboundedCoproducts`
without changing their signatures or definitions. The proofs derive the fibre-dimension
integer bound, apply the proper unbounded window theorem, supply ambient coproduct and
truncation data, and invoke the bounded-family theorem along the original unit route.

Two new modules retain and complete categorical arguments from the interrupted attempt:
`ProperUnboundedCoproductComparison` transports colimit cofans along the canonical
cohomology window zigzag, and `DerivedTruncationCoproducts` proves preservation of arbitrary
coproduct cofans by double good truncation. Upper truncation is proved using the homology
coproduct comparison, naturality and vanishing. Lower truncation reuses the already proved
private generic theorem in `EllAdicProperLocalizingCoproducts` through `import all`.
The existing public proper localizing theorem of that module is not used.

Both new public theorems have new DAG nodes; the item's node records how the six original
steps use them. All three delivered modules compiled individually through `lcompile.py --all`,
without errors or warnings (5.5 s, 1.7 s and 6.4 s respectively).
No existing statement, definition or visibility changes. No consumer
adaptation is required. The elaboration-option commands and new helper APIs are recorded in
`coord/changes/proper-unbounded-coproduct-proof-helpers.md`. Empty families, zero objects, arbitrary integer
cutoffs (including an empty window), and the original geometric fibre-bound edge cases
are retained.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.ProEtale.properUnbounded_preservesCoproducts`
- `AlgebraicGeometry.ProEtale.properUnbounded_preservesCoproducts_padicAlgCl`

Also proved both new helper theorems:

- `AlgebraicGeometry.ProEtale.properUnbounded_coproductComparison`
  (`lem-sfb-proper-coproduct-window-transport`).
- `AlgebraicGeometry.ProEtale.derivedTruncation_coproducts`
  (`lem-sfb-derived-truncation-coproducts`), closing the retained helper hole.

No holes added. No `sorry` remains in any delivered module. The existing proper-window,
ambient ind-constructible closure and bounded-family declarations remain dependencies;
their proofs are separate project items, as the stage requires.

## No longer needed

Removed the item's redundant direct proof imports
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` and
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. The proof uses standard
truncations through their existing APIs; no sequential homotopy-colimit construction is
used. The generic truncation and cohomological-isomorphism DAG dependencies remain needed.
No unit step or mathematical dependency is bypassed. No whole module is asserted to leave
the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The retained comparison helper had a naturality simplification that did not reduce
`Discrete.functor` object wrappers. `simpa [Category.assoc]` proves the required equation
without changing its signature. The main proofs also needed explicit coproduct and exactness
instances for the pulled-back target module category. The interrupted sandbox had no DAG
records for its two new modules; these are now supplied, and its last helper hole is proved.
No mathematical statement was disputed.

## New nodes

`lem-sfb-derived-truncation-coproducts` records double good truncation preserving a colimit
cofan of arbitrary derived module objects. It has no constructibility or boundedness
hypothesis and no remaining hole.

`lem-sfb-proper-coproduct-window-transport` records the categorical combination of the
window, sum-closure, homology, truncation and bounded-family assumptions. Its complete Lean
proof transports the truncated image cofan in each cohomology degree and identifies the
canonical comparison by its coprojections. It has no remaining hole.

Change record: `coord/changes/proper-unbounded-coproduct-proof-helpers.md`.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
