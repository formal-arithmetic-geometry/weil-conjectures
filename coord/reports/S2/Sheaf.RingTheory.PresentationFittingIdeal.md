## What changed

Proved `LinearMap.presentationFittingIdeal_independence_baseChange` from the DAG's
existing statements, keeping all public definitions and the theorem signature unchanged.
Added private proof imports for row-minor stable invariance, common stabilization of
finite free surjections, and row-minor scalar extension.

The private bridge `presentation_eq_row` compares the span over arbitrary column
embeddings with the row-minor ideal defined using increasing column subsets. Sorting
columns gives a permutation; its determinant sign preserves ideal membership. The reverse
inclusion selects the ordered rows and columns of each minor.

For independence, transport the common stabilization through explicit finite-coordinate
splitting equivalences and apply row-minor stabilization and coordinate invariance.
For base change, tensor right exactness identifies the kernel with the image of the
tensored kernel inclusion. The scalar-extension lemma's tensor-coordinate formula
identifies its equivalence with `TensorProduct.piScalarRight`, and its image and ideal
clauses give the desired equality. Localization follows by composing with the canonical
localization tensor equivalence; an injective equivalence preserves the relation kernel.

The proof includes the unit-ideal branch `n ≤ k` explicitly. It requires neither
flatness nor a finitely generated kernel. Empty finite free modules, the zero ring,
and localization at zero remain included in the unchanged statement.

Validation: the delivered file compiled cleanly through `lcompile.py` in 6.6 seconds
(exit code 0, no diagnostics). A static comparison confirmed that the existing public
definition bodies and theorem signature are unchanged, the source contains no `sorry`,
and every line is at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`LinearMap.presentationFittingIdeal_independence_baseChange`
(node `lem-trf-fitting-ideal-independence-base-change`). No holes remain in the item.
Added 0 holes and split off 0 statements. All private helpers are proved.

The proof uses the existing declarations
`Module.free_surjections_common_stabilization`
(node `lem-trf-free-surjections-common-stabilization`) and
`Matrix.rowMinorIdeal_scalar_extension`
(node `lem-trf-row-minor-ideal-scalar-extension`), whose existing holes are not changed
by this delivery. The proof of the already stated row-minor invariance theorem also
uses `Matrix.minorIdeal_inclusions`; that existing downstream hole is unchanged.

## No longer needed

Removed the direct proof import
`Sheaf.LinearAlgebra.Matrix.MinorIdealInclusions`: the item now uses the stronger,
already stated `Matrix.rowMinorIdeal_stable_invariance` interface. The minor-inclusions
module remains a dependency of that interface and is not withdrawn or claimed pruned.
All five declared DAG proof dependencies remain needed. No nodes or modules are pruned;
no additional split statements are introduced. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The Lean file's eight-step docstring predates the DAG's
existing four-step assembly through its three auxiliary statements. The proof now
implements that assembly. No statement or definition repairs were needed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
