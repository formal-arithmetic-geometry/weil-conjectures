## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.completed_constant_unbounded_finite_diagram_comparison`
by a reduction through one scalar extension at the completed coefficient ring.
The original statement, universes, binders and public imports are unchanged.

The proof constructs the single coefficient map from the limit lift of
`constantAdicFiniteCone`, proves its projection equations, and obtains the finite
isomorphisms from `pbcReductionNormalization`. Private proved helpers establish
ordinary and derived restriction associativity, normalization associativity,
normalization compatibility with semilinear transitions, and transition naturality.
The final square is proved for arbitrary comparable indices, including equality.

Added the proof import `Sheaf.Paper.CompletedConstantDerivedScalarFactorization`
and a private import of all declarations of
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`. The latter supplies
its already proved generic `exactComp_assoc` helper; this is used as a general
exact-derivation coherence tool, not as a replacement route through another unit.
No existing module besides the assigned item is changed.

## Proved and sorry left

Original holes closed: 1, in
`AlgebraicGeometry.Scheme.completed_constant_unbounded_finite_diagram_comparison`.
The item now has zero sorries. Its theorem is proved from the newly isolated scalar
factorization and the existing normalized scalar-extension API.

New holes added: 1, in
`AlgebraicGeometry.Scheme.completed_constant_derived_scalar_factorization`, node
`lem-weil-pbc-completed-constant-derived-scalar-factorization`.
This is a decomposition, with net hole reduction zero; it is not a complete proof
of the underlying unbounded realization comparison.

The new obligation compares functors at the completed coefficient ring and contains
no finite quotient isomorphisms, indices or semilinear transition condition.
All construction and coherence of the finite quotient diagram are proved here.
In particular, neither the existence of the requested finite family nor its
compatibility is assumed in the new statement.

Validation: both modules compiled through lcompile.py. The final item compilation
completed in 8.7 seconds without warnings; the new scalar-factorization statement
compiled in 6.4 seconds with its declared sorry. Delivery preflight is performed
by deliver3.py. The original theorem signature was also
compared verbatim against the repository version. The proof-dependency lists agree
with the unions of proof-step dependencies. All new Lean lines have at most 100
characters.

## No longer needed

The bounded finite-complex dependency
`lem-weil-pbc-completed-constant-finite-complex-realization` /
`Sheaf.Paper.CompletedConstantFiniteComplexRealization` is not used or imported:
its resolution comparison has a bounded finite source, whereas this item allows
arbitrary E. It is removed from this node's proof dependencies.

`lem-weil-pbc-completed-constant-sheaf-reduction` is not directly used for its
finite reduction comparison; its module remains transitively imported by the
unchanged public data imports and is not claimed as globally pruned.

`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is no longer a direct proof
dependency of this item; it remains a planned dependency of the new scalar
factorization. The two definition dependencies remain available through the
unchanged public imports. No existing public import or library module is removed,
and no whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned bounded finite-complex comparison does not provide a comparison for an
arbitrary unbounded E. The proof therefore separates the single completed-scalar
comparison from finite reduction, and proves the finite coherence categorically.
No statement is weakened or marked disputed. The unit route is unchanged.

The source calculation is Stacks sites-cohomology.tex, 06YY
(lemma-derived-base-change), 06YU (definition-derived-tor), 0G7E
(lemma-pullback-K-flat), and 0D6D (lemma-derived-pullback-composition). The new
obligation follows the composition argument with the specified coefficient maps;
its full natural-language proof is in its docstring and node.

Edge cases: the categorical helpers impose no invertibility, flatness, finiteness
or distinctness assumptions on successive ring maps. Thus identity transitions,
zero rings and zero complexes are included. The scalar factorization also includes
identity scheme maps, the empty scheme, and ideals zero or top: the same limit cone,
unit-factor tensor maps and exactness assumptions still apply.

## New nodes

`lem-weil-pbc-completed-constant-derived-scalar-factorization`, in
`Sheaf.Paper.CompletedConstantDerivedScalarFactorization`, is the single
completed-coefficient tensor/pullback computation preceding finite reduction.
Unlike the assigned statement, it has no finite diagram and no transition square.
The item now proves the passage from this factorization to the entire finite
diagram. Lean Finder, Loogle and Mathlib grep were run through msearch.py, with
queries and actual results recorded in the node. A blueprint search and repository
signature search found no existing statement of this factorization.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
