## What changed

Constructed the coefficient-functor deletion complexes, coordinate pullbacks, and signed
vertex prisms explicitly in `Sheaf.CategoryTheory.InternalFunctionVertexPrism`. All
existing public signatures and definitions are preserved. The only added import in the
item is the private proof import `Sheaf.CategoryTheory.ProfiniteVertexPrismBoundary`.

Parameter precomposition is a real construction: precompose the natural families of
`InternalFunctions.evaluate`, apply its inverse, prove sectionwise linearity and
restriction compatibility, and lift along the existing fully faithful section-module
functor. Evaluation injectivity proves functoriality. No data is selected from an
unproved existence theorem. Mathlib's alternating coface complex supplies deletion
squared. Evaluation as an additive homomorphism proves the differential and prism
formulas on every slice. Coefficient naturality, both parameter naturalities, and the
degree-zero identity and evaluation formula are proved.

The auxiliary module defines the continuous tuple operators and proves deletion squared,
coordinate/differential compatibility, both prism naturalities, and the degree-zero
boundary. The positive-degree signed cancellation is isolated as a theorem about an
arbitrary contravariant functor into a preadditive category. The main theorem combines
this algebraic boundary with the independently constructed internal maps and all their
formulas. The item's DAG proof and proof dependencies follow this construction.
Both files were accepted by the launcher compiler: about 6 seconds for the auxiliary
module and 30 seconds for the item. The final delivery checks validate the cleaned sources.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.CondensedBar.internal_function_vertex_prism`
(node `lem-sfb-internal-function-vertex-prism`). Its complete Lean proof constructs every
field of the original specification.

Added one hole:
`CategoryTheory.CondensedBar.TupleOperators.prism_boundary`
(node `lem-sfb-profinite-vertex-prism-boundary`, module
`Sheaf.CategoryTheory.ProfiniteVertexPrismBoundary`). This is precisely the
positive-degree finite signed-sum cancellation, with its source and pairing/telescoping
proof in its docstring. It constructs no internal maps or complexes and asserts no
evaluation formulas or naturality. All auxiliary definitions have actual bodies; every
other auxiliary theorem is proved.

This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes closed. The item has zero remaining holes; the delivery has one.

## No longer needed

The item's proof no longer needs
`lem-sfb-profinite-free-hom-resolution-evaluation` or its module
`Sheaf.CategoryTheory.ProfiniteFreeHomResolutionEvaluation`: the generalized-function
equivalence already contained in `InternalFunctions` constructs parameter precomposition
and detects equality, so the product-evaluation and derived-resolution comparison is
unnecessary here. It was a DAG proof dependency, not an existing Lean import; no
original imports were removed. This is a dependency pruned from this proof, not a claim
that the evaluation module is globally unused or should be withdrawn.

The original informal deletion-squared calculation is replaced by the existing Mathlib
`AlgebraicTopology.AlternatingCofaceMapComplex.d_squared`. No other declared dependency
or blueprint unit step is bypassed. No source-library declarations or modules are removed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan's product-evaluation step was stronger
than needed: `InternalFunctions.evaluate`, its injectivity, and its recorded linearity,
restriction and coefficient formulas suffice directly. This avoids bringing in the
substantial resolution-comparison specification for a construction having no resolution.

The edge cases need no additional assumptions: precomposition and finite sums choose no
vertex, so empty parameters, zero coefficients, and equal endpoint maps remain included.
The new algebraic boundary has the same integral cancellation in these cases; its
remaining proof explicitly describes the inverse pairing and endpoint telescope.

## New nodes

`lem-sfb-profinite-vertex-prism-boundary` records the pure positive-degree signed
vertex-insertion boundary for every contravariant profinite functor into any
preadditive category. Its module also contains the concrete tuple operators and the
proved elementary compatibilities used in the main construction. Searches by
LeanSearch, Loogle, LeanFinder and Mathlib/source text found abstract alternating
complex and homotopy machinery, but no ready-made theorem supplying these particular
continuous vertex-insertion identities. The blueprint search found no duplicate.
The source is Stacks `simplicial.tex`, Tag 019S,
`equation-homotopy-to-homotopy` and the cancellation before `lemma-homotopy-s-N`.
No shared-interface change or change record is needed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
