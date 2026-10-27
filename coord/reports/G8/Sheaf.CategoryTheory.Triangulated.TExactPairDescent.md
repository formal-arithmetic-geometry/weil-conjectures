## What changed

Filled `CategoryTheory.CommonStage.tExactPairDescent` in
`Sheaf.CategoryTheory.Triangulated.TExactPairDescent`, preserving its statement and all
existing definitions and public imports. Private helpers identify canonical quotient
structures, apply the declared coherent additive descent theorem, establish the descended
shift comparison on representatives, and transport distinguished triangles and both
indexed t-structure halves. The stage equality and extension representative are computed
using the normalized unit comparison.

The change record `coord/changes/tExactPairDescent-private-helpers.md` documents
the closed private-helper section commands flagged by the static interface check.
No global instance is added; additive identity comparisons are installed locally.

The proof follows all six steps of `lem-a1-texact-pair-descent`. It uses the original
`CommonStage` interface reexported by `StageSystemFunctorDescent`; no additional
associator/shift coherence or faithfulness hypothesis is introduced.

## Proved and sorry left

The delivery fills the single original hole,
`CategoryTheory.CommonStage.tExactPairDescent` (node `lem-a1-texact-pair-descent`).
There are no textual holes in the item and no holes added elsewhere. No statements are
split off. The existing dependency `CategoryTheory.CommonStage.coherent_pair_functor_descent`
remains an imported theorem and is not claimed as proved by this delivery.

Validation: the complete proof compiled without errors or warnings in 13.7 seconds.
The final local-instance adjustment is being rechecked by delivery preflight. The existing definitions, public imports, and theorem signature were
checked byte-for-byte against the shared source and are unchanged. The packet adds
zero holes and changes no other Lean module.

## No longer needed

None. No imports, declarations, modules, nodes, or approved tool uses are withdrawn.
The proof retains the prescribed coherent additive descent, triangulated-category,
t-structure, and common-stage quotient calculus dependencies and the unit route.

## Where the brief, the DAG or earlier work was wrong

The generic descent theorem supplies its own canonical `PairStructure` for each diagram,
whereas this item supplies arbitrary canonical structures through its presentations.
The proof explicitly identifies those structures by the identity map on the same quotient
Hom types, proving its functor and additive laws from the canonical formulas. This is
glue required to apply the stated dependency; no statement repair is needed.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
