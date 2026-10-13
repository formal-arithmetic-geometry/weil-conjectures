## What changed

The target module now reduces its construction to two named intermediate statements: a pinned
functorial relative Mayer--Vietoris triangle comparison and a generic endpoint cone presentation.
The target compiles with these imports. Both intermediate proofs remain explicit named holes because
their constructions require the full derived-category mate and cylinder calculations.

## Proved and sorry left

The target declaration `AlgebraicGeometry.relativeMV_cone_presentation` is closed by a complete Lean
reduction to the two strictly smaller intermediate statements. Sorry remains in
`AlgebraicGeometry.relativeMV_pinned_triangle_comparison` (node
`lem-pc-relative-mv-pinned-triangle-comparison`) and in
`derived_endpoint_cone_presentation` (node
`lem-pc-derived-endpoint-cone-presentation`).

## No longer needed

The original direct proof imports `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`,
`Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine` are no longer proof dependencies of the target after
this reduction. The target now imports only the two intermediate modules and `RelativeMVMaps` plus
the statement-level derived-category and morphism imports.

## Where the brief, the DAG or earlier work was wrong

The original proof plan concealed two substantial steps: constructing the pinned morphism of
relative Mayer--Vietoris triangles and strictifying its derived-category cone diagram. These are
now separate named statements rather than an assertion that arbitrary vertex identifications can
be chosen coherently.

## New nodes

`lem-pc-relative-mv-pinned-triangle-comparison` states the functorial pinned triangle morphism;
its module is `Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison`.
`lem-pc-derived-endpoint-cone-presentation` states the generic endpoint cone strictification;
its module is `Sheaf.CategoryTheory.DerivedCategory.EndpointConePresentation`.

## Second reading by T4

1. I compared `RelativeMVConePresentation.lean` with the repository version. The theorem
   signature and all existing declarations are unchanged byte for byte; only proof-only imports
   and the target proof body differ.
2. I compiled all three delivered modules with `lcompile.py --all`. Compilation succeeds. The
   only remaining `sorry`s are the two named split theorems, and there are no hollow definitions,
   axioms, unsafe declarations, or forbidden implementation hooks.
3. The split statements are strictly smaller than the target: one supplies the pinned
   distinguished-triangle morphism and the other supplies the generic strict cone presentation.
   Their docstrings give complete construction arguments and each has a matching DAG node.
4. The target proof follows exactly the two proof steps recorded in its DAG node and uses the
   displayed commutativity equation to invoke the endpoint presentation. The unit route through
   the pinned triangle and endpoint cone nodes is retained.
5. I checked the imports and DAG records. The target now needs only `RelativeMVMaps`, the
   statement-level derived-category/morphism imports, and the two proof-only intermediate
   modules; the four former direct-construction imports are pruned and listed above.

Changed during second reading: no theorem statements or definitions; only this report was added.
