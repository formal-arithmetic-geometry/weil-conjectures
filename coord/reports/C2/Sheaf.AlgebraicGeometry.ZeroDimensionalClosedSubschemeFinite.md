## What changed

Proved `AlgebraicGeometry.closed_subscheme_finite_of_topologicalKrullDim_le_zero` in
`Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite`, preserving its signature and
all import visibility. Give Z the composite structure morphism, supply its finite-type and
quasi-compact instances, convert the dimension bound with `Scheme.dim_eq_topologicalKrullDim`,
and apply the already stated `isAffine_and_isFinite_of_dim_le_zero`. The global-sections
conclusion follows by composing `Scheme.Hom.finite_appTop` with the finite inverse of
`Scheme.ΓSpecIso`. Updated the declaration's proof docstring and its node's proof route.

The item compiles cleanly through lcompile.py (2.8 seconds). No definitions, statements,
consumer modules, or public imports changed. The source read was Stacks varieties.tex,
`lemma-algebraic-scheme-dim-0` (Tag 06LH), and morphisms.tex, the opening of Section 03J3.
The unit record sk-thm-picard-rr has empty realized statement/steps lists; its route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.closed_subscheme_finite_of_topologicalKrullDim_le_zero`
(node `lem-pc-zero-dimensional-closed-subscheme-finite`).

Holes left in the item: zero. Holes added: zero. Split-offs: zero.
The proof uses the existing stated dependency
`AlgebraicGeometry.isAffine_and_isFinite_of_dim_le_zero`
(`lem-pc-algebraic-dim-zero-affine-finite`, module
`Sheaf.AlgebraicGeometry.DimZeroFiniteOverField`), whose proof is still sorry in the library.
Thus this closes the assigned hole from existing declarations, not all transitive axioms.

## No longer needed

Removed proof dependency `lem-weil-pbc-closed-immersion-proper`: properness is unnecessary,
since Mathlib's closed-immersion-to-finite instance already supplies finite type and
quasi-compactness. Its module was not explicitly imported, so no import removal is needed.
Both proof imports, `Sheaf.AlgebraicGeometry.DimZeroFiniteOverField` and
`Sheaf.AlgebraicGeometry.Dimension`, are used and retained. No other node or module is pruned.
The separate empty-scheme argument in the old plan is unnecessary because the existing
zero-dimensional finiteness statement already accepts dimension ⊥.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or definition found. The old plan required an unnecessary empty/nonempty
case split and a detour through properness. The declared dimension-zero lemma is applicable
uniformly, including the empty scheme. The finite-dimensional conclusion uses exactly the
specified ΓAlgebra, by the finite composite ring map, without choosing a new algebra structure.
Searches through msearch (LeanFinder, Loogle and grep), and local searches of Mathlib,
WeilConjectures and Sheaf, confirmed the existing dimension-zero dependency and the Mathlib
finite_appTop API suffice. No new nodes or change records are needed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
