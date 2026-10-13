## What changed

Replaced the hole in `AlgebraicGeometry.relative_open_difference_diagram` with actual
adjunction constructions and explicit maps. Proved the compatibility equation by
homEquiv cancellation, additivity and naturality. Proved triangular matrix inverses,
including the swapped matrix needed on V, and transported them through the restriction
functors' biproduct comparisons. Proved invertibility of the derived open counits from
fully faithful pushforward. All original signatures and visibility are unchanged.

Added the proof-only imports of the existing derived adjunction and fully-faithful
right-derived-functor modules and the new `DerivedOpenCrossComponentsIsIso` module.
The latter isolates only the geometric invertibility of two individual components.
It does not assert existence of d, projections, a compatibility equation, a biproduct
matrix isomorphism or a gluing object. No data are chosen from its unproved theorem.

Both delivered modules compile locally without warnings. The parent compilation
is about 30 seconds. The unit has no realized nodes or steps to bypass.

## Proved and sorry left

Closed the original hole of `AlgebraicGeometry.relative_open_difference_diagram`
(node `lem-sc-relative-open-difference-diagram`) by a complete Lean reduction.
There are no sorries in the item's module.

Added one hole: `AlgebraicGeometry.derived_open_cross_components_isIso`
(node `lem-sc-derived-open-cross-components-iso`). This is a decomposition,
not a net reduction in holes: one closed and one added. The explicit maps,
compatibility equation, matrix inverses and counit invertibility are proved.

## No longer needed

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` from the parent module.
Its node `lem-pc-restrict-derived-direct-image-open` is now needed only by the new
cross-component item; its module remains imported there and is not globally pruned.
The definitions of derived direct image and derived restriction remain needed.
No original node or module is globally pruned. No unused imports remain.

## Where the brief, the DAG or earlier work was wrong

The plan's Tag 08FE declaration gives `Nonempty` of a natural functor isomorphism.
Its statement does not say that the particular adjunction-defined cross-component
map is invertible under that comparison. A proof cannot use unspecified coherence
from the dependency's proof. The new statement records exactly this missing geometric
step; the parent does all remaining constructions and algebra in Lean.

Read Stacks Tags 08DG and 08FE on their public pages. The local literature checkout
contains only indexes, so the existing cited source was read online. Empty opens,
empty intersection, equal opens and an entire open impose no extra hypothesis: the
same component calculation applies, and the zero-category case has invertible unique
maps. For arbitrary adjunction structures, natural automorphisms of right adjoints
conjugate the components, so the new statement does not rely on a hidden normalization.

The blueprint search for `difference` found five unrelated imported nodes; the
ancestor tool returns None for this recently created item. The new node retains the
same nearest ancestor named in the item's existing blueprint.from record,
`lem-sc-finite-duality`, and records the precise restriction step and via item.

## New nodes

`lem-sc-derived-open-cross-components-iso`, in
`dag/nodes/sec-picard-framework/lem-sc-derived-open-cross-components-iso.json`,
states invertibility of the adjoint overlap counit on the opposite open, for the
specified canonical restriction comparisons. It is strictly below the difference
diagram construction. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedOpenCrossComponentsIsIso.lean`.
LeanSearch was unavailable (HTTP Internal Server Error); LeanFinder returned
underived open counit lemmas, and Mathlib grep found no exact derived cross-component
statement. The actual queries and results are logged in searches.jsonl.
No definitions or interfaces were changed; no change record or forced adaptation
is needed.

## Second reading by B4

1. Compared `lean/Sheaf/AlgebraicGeometry/RelativeOpenDifferenceDiagram.lean` with the repository version. Existing declaration signatures and visibility are unchanged; only proof-only imports, private proof helpers, and the target proof differ. The new module and DAG node are included as declared.

2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The parent target has no `sorry`; the only remaining hole is the named split theorem `AlgebraicGeometry.derived_open_cross_components_isIso`, with its matching node and proof docstring. No forbidden declarations or hollow definitions occur.

3. Checked the target proof's explicit adjunction maps, counit invertibility, triangular matrix inverses, biproduct transport, and compatibility calculation. The target statement is unchanged and the new split statement is strictly below it, asserting only the two component isomorphisms required by the matrix argument. Its edge cases and absence of a covering hypothesis are documented.

4. Checked imports and DAG proof dependencies. The removed parent import is retained through the new cross-component module, and no globally prunable original node is claimed. The target node's proof and `proof_deps` follow the Lean route; the unit has no realized entries to bypass.

5. Searched the repository and Mathlib for an existing derived cross-component theorem; no matching result exists (search details are in `searches.jsonl`). The new node has source, proof steps, dependencies, Lean declaration, and blueprint metadata matching the module.

Changed only the report by adding this review record; no Lean statement or definition was changed.
