## What changed

Proved `CategoryTheory.cohomology_mem_of_filtration` in
`Sheaf.Paper.EtaleLisseFiltrationDevissage`, with its statement and public imports unchanged.
Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle` to use the
already-proved bounded-below short-exact-sequence triangle.

The proof uses `cohomology_in_weak_serre_subcategory` to obtain the triangulated
cohomology class, then pulls it back along the composite of the given functor and
`DerivedCategory.Plus.ι`. Induction on `Fin (r + 1)` starts with the bottom subobject,
which is zero. For each inclusion, `ShortComplex.exact_cokernel` gives the short exact
sequence and `singleTrianglePlus_distinguished` gives its distinguished triangle.
Middle-vertex closure combines the induction hypothesis with the quotient hypothesis.
Finally, the top subobject's arrow gives the isomorphism to `X`.

This implements the existing node's four proof steps without a route change or new
nodes, and retains the unit route. The source is Stacks Tag 0GKY, final paragraph of
`lemma-loc-constant-shriek-rel-dim-1`, with Tag 06UQ and the canonical derived triangle.
The proof covers `r = 0`, repeated subobjects and zero quotients without extra cases.
LeanFinder, Loogle and grep searches found no replacement for the filtration theorem;
local library search found the proved bounded-below triangle interface above.

Validation: the complete module compiled cleanly through `lcompile.py` (1.5 seconds).

## Proved and sorry left

Closed 1 hole: `CategoryTheory.cohomology_mem_of_filtration`
(node `lem-weil-pbc-etale-lisse-filtration-devissage`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
No declarations, statements, definitions or proofs in other modules were changed.

## No longer needed

None. No imports were removed, no nodes or modules were pruned, and every dependency
of the existing DAG argument remains used. Both proof-only imports are used.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The source library already supplies the
bounded-below lift of the short-exact-sequence triangle, so no new lifting lemma is
needed. No definition repair or consumer adaptation was necessary.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
