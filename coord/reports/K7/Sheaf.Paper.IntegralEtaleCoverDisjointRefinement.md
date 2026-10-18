## What changed

Proved `AlgebraicGeometry.integral_etale_cover_disjoint_refinement` in
`Sheaf.Paper.IntegralEtaleCoverDisjointRefinement`, with its original signature and visibility.
The proof applies the existing source-library theorem
`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover` from
`WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover` to the sieve generated
by the original covering family. Its implementation already carries out the DAG's
standard-etale finite-subalgebra reduction, finite pointed-piece refinements, shrinking,
and pullback. This delivery supplies the interface conversion: a geometric point from
an algebraic closure of the residue field, the jointly-surjective covering sieve,
factorizations through the original members, the ordinary marked point, and transport
across pullback symmetry. Disjointness, covering, and the final morphism equation are
proved explicitly. No definition, statement, consumer module, or mathematical route changes.

Added proof-only imports of `WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover`
and `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`. All four public imports are retained.
The theorem-local transparency setting supports the existing small-etale category API.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.integral_etale_cover_disjoint_refinement`
(node `lem-sbc-integral-etale-cover-disjoint-refinement`).
Added 0 holes and split off 0 theorems. No `sorry` remains in the delivered module.
The original arbitrary covering-index universe and the empty decomposition are preserved.

## No longer needed

Removed redundant direct proof imports:

- `WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`

Their declarations remain needed transitively by the existing integral disjoint-cover
implementation; this is import simplification, not a claim that their nodes or modules
leave the target closure. No DAG nodes or modules are pruned. The unit route and the
seven mathematical steps in the existing node are retained through the source proof.

## Where the brief, the DAG or earlier work was wrong

The existing import list named low-level inputs but omitted the source library's completed
integral disjoint-cover theorem, which already implements the complete planned geometric
argument. Searches for disjoint integral refinements found this theorem; Loogle returned
no match, LeanFinder returned site and covering infrastructure, and the Mathlib grep
returned no theorem constructing this refinement. The source text read was Stacks
`etale-cohomology.tex`, `lemma-simplify-B`, `lemma-finite-B`, and `lemma-integral-B`
(Tags 04DP, 04DQ, 04DR). No mathematical statement error was found.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
