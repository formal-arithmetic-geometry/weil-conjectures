## What changed

Proved `CategoryTheory.BigradedExactCouple.edge_collapse` in
`Sheaf.CategoryTheory.EdgeCollapse`, with its complete signature and docstring unchanged.
The proof follows the existing node `lem-sp-edge-collapse` and its source proof paragraph:

- Off-column zero terms remain zero on all subsequent pages, since homology is a
  subquotient. The differential's positive first-index shift forces every differential
  to be zero; the transported incoming differential is therefore also zero.
- The cycle/boundary recursion becomes stationary. Its GLB/LUB properties identify the
  limiting cycles/boundaries with those at the starting page. Epimorphic quotient
  comparisons give the page isomorphisms and both required projection equations.
- Weak convergence identifies the associated graded with the limiting page. All graded
  pieces except degree zero vanish. Integer induction and the finite filtration bounds
  give F^0 = top and F^1 = bottom. The inverse of the top-step inclusion followed by the
  degree-zero quotient and the convergence/page comparisons constructs the requested
  abutment isomorphism. Its compatibility with the original cocone map is proved.

All helper results are private and completely proved in the item module. The only new
proof import is `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru`, whose
proved factorization criteria handle pullbacks of the zero subobject. The existing DAG
proof plan and all three proof dependencies are unchanged.

The source-library edge-collapse theorem was inspected, but its all-index ExactCouple
representation differs from this theorem's BigradedExactCouple and cycle-boundary tower.
A representation comparison would add unnecessary work. Mathlib search through
leanfinder, loogle and grep found no direct theorem for this exact representation.

Change record: `coord/changes/s9-edge-collapse-prune-imports.md`.
The complete item compiles through lcompile.py with no errors or warnings (2.1 seconds).

## Proved and sorry left

Closed one hole: `CategoryTheory.BigradedExactCouple.edge_collapse`
(node `lem-sp-edge-collapse`). Proved 1 of 1 original sorries. Zero sorries remain in the
item, zero holes are added elsewhere, and no result is split off. This is a complete
proof, not a decomposition into new unfinished statements.

## No longer needed

Removed the unused public imports `Sheaf.CategoryTheory.ExactCouple` (already an empty
withdrawn compatibility module) and `Sheaf.CategoryTheory.Filtration` (its compatibility
API is not used here). Both leave this item's import closure. No Lean file is withdrawn.

No DAG dependency is pruned: `def-sp-exact-couple`, `def-sp-convergence`, and
`def-sp-filtration` all remain mathematically needed, supplied by the upstream exact
couple, convergence, and PBC filtration APIs. No unit or chapter step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The rework row records an older missing-public-import failure. The current source already
contains T6's restored public convergence import, so this delivery starts from that
current module and closes its remaining proof hole. The rework archive is neither deleted
nor treated as withdrawn mathematics.

No mathematical error in the node or unit route was found. The proof explicitly handles
r0 = 2, arbitrary later pages, negative bidegrees and filtration bounds on either side of
zero. It does not assume that the original page two is already concentrated in one column.
The finite filtration bounds are used without any extra boundedness assumption on the
initial page or any infinite completeness assumption on the subobject lattice.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
