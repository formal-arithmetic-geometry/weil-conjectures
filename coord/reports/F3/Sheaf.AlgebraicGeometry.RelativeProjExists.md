## What changed

Proved `AlgebraicGeometry.exists_relativeProjData` with its original signature. The
construction is an explicit relative gluing of the specified local Proj models over
all affine opens. Its restriction identifications come from the images of the colimit
injections. The comparison with any other realization is the unique comparison of
colimits after identifying its charts with the pullback of the directed affine cover.

Added `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`, attached to the existing
node `lem-nagata-proj-affine-restriction`. It proves the cartesian restriction squares,
identity, and composition. The algebraic bridge uses the existing quasi-coherent affine
section base-change theorem and the source library's affine Proj base-change theorem.
Private, proved helpers identify the additive-subgroup grading with the submodule grading
and extract degreewise base change from total base change using direct sums.

Updated the two existing nodes' proof plans and Lean attachments. Change record:
`coord/changes/F3-relative-proj-exists-proof-scope.md` documents the file-level scope
commands flagged by preflight and audits every downstream importer. No source-library
file, public definition, existing declaration signature, or target was changed.

## Proved and sorry left

Closed the one assigned hole: `AlgebraicGeometry.exists_relativeProjData`
(`lemma-nagata-relative-proj-exists`).

Added zero holes. The three public results
`AlgebraicGeometry.RelativeProjAlgebra.localTransition_isPullback`,
`AlgebraicGeometry.RelativeProjAlgebra.localTransition_id`, and
`AlgebraicGeometry.RelativeProjAlgebra.localTransition_comp`
(`lem-nagata-proj-affine-restriction`) and all private helpers have complete proofs.
There are no remaining `sorry`s in either delivered module. This is a proof, not a
split-off decomposition. Existing prerequisite holes are left with their existing owners.

## No longer needed

Removed the proof imports `Mathlib.AlgebraicGeometry.Gluing` and
`WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` from the item. The new proof uses
`Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction` and the relative-gluing and
directed-cover API already publicly imported by `RelativeProjData`.

The current blueprint's `lemma-nagata-proj-chart-ring-cocycle` is not separately
needed: `Proj.map_comp` proves the transition cocycle directly. No import or new
proof of that chart-ring lemma is required by this route.

The item's original mathematical dependencies remain: directed-cover colimits implement
morphism gluing, and the directed affine cover implements the affine-basis refinement.
The removed direct Mathlib gluing import was redundant through `Cover.Directed`.
No module or declaration is withdrawn, and no claim is made that either removed
import leaves the global target closure.

For the affine-restriction node, the following former direct proof dependencies are
no longer required separately: `def-weil-pbc-graded-sheaf-structures`,
`lem-weil-pbc-quasi-coherent-module-coproduct-closure`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-quasi-coherent-algebra-affine-inclusion`, `def-weil-affine-spectrum`,
`def-weil-open-immersion`, `def-pc-fibre-product`,
`def-nagata-homogeneous-localization-degree-zero`, and
`lem-weil-pbc-scheme-morphism-gluing`. The input already supplies the internal grading;
the existing total-section base-change theorem and affine Proj base-change primitive
replace their expanded arguments. The canonical affine inclusion spectrum identity is
recorded explicitly instead. These are local dependency reductions, with no claim of
global pruning where other consumers remain.

## Where the brief, the DAG or earlier work was wrong

The affine-restriction dependency existed as a mathematical DAG node but had no Lean
attachment. The source library's relative Proj uniqueness theorem has an affine graded-section
data input, and does not directly prove this retained interface on graded algebra
sheaves. This delivery supplies the missing affine-restriction bridge and preserves the
source-library theorem and attachment.

The current blueprint's overlap cocycle is implemented by the functor laws for
`Proj.map` over the directed affine basis. Pullback stability of the directed cover
handles non-affine intersections. The unit has no proof steps to bypass. Empty schemes,
the zero ring, degree-zero-only algebras, and equal affine opens require no additional
hypotheses; in particular the proof never assumes degree zero equals the structure sheaf,
finite generation, or affine intersections.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
