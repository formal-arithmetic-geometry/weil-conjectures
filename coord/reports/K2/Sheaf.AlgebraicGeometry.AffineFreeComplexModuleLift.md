## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_module_lift` in
`Sheaf.AlgebraicGeometry.AffineFreeComplexModuleLift` without changing its statement or
visibility. The complex is the original complex's global sections with negated degrees.
Its finite bases come from the supplied sheaf identifications, `freeSectionsEquiv`, and
`ΓSpecIso`. A fully proved private matrix calculation identifies each lifted coefficient
with the image of its sheaf coefficient, so `IsUnit.map` transfers the supplied pivot.
The associated-sheaf comparisons are the canonical counit isomorphisms, and their
naturality proves differential compatibility. The two private coordinate constructions
contain real data and complete proofs; no data is chosen from an unproved existence theorem.

Updated the item's DAG proof and proof origin to this route. All original public imports
and all public signatures are unchanged. No new module, node, or interface change was needed.
The existing declaration docstring records the original valid finsupp plan; the implemented
shorter global-sections route is recorded in the DAG and the proof's inline comment.

Read [Stacks 01HV](https://stacks.math.columbia.edu/tag/01HV) (global sections of the
structure sheaf and associated sheaf, and functoriality) and
[Stacks 01I7](https://stacks.math.columbia.edu/tag/01I7) (the associated-sheaf mapping
property), together with the corresponding Mathlib constructions and their signatures.
The sources are not installed under this clone's `literature/`, so these pages were read
online. No new unproved statement requires a literature request.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_module_lift`
(node `lem-pc-affine-free-complex-module-lift`). This is a proof, not a decomposition:
1 original hole closed, 0 new holes added, and no `sorry` remains in the delivered module.
The private helpers `freeCoordinates`, `affineFreeCoordinates`,
`freeCoordinates_symm_single`, and `affineFreeCoordinates_matrix` are completely proved.

The module compiled cleanly with `lcompile.py`. The delivery dry run additionally checks
the axiom probe and the stage-3 preflight. The proof uses no nontriviality hypothesis;
empty bases cause no problem in the coordinate construction, and the supplied indices
already exclude them in the pivot degrees. Negative and positive degrees are handled
uniformly by the chain shape proof and explicit index casts.

## No longer needed

None of the original imports, nodes, or modules can be removed: the affine free-module
comparison `lem-weil-pbc-spec-tilde-free-module` is still used to invert the counit, and
the four public imports are needed by the statement's objects and operations.
The separate preimage-of-differential construction and the coproduct-injection coefficient
calculation of the original plan are unnecessary. They were not separate DAG nodes, so
no module is claimed pruned. An experimental proof import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` was removed before delivery;
zero preservation is proved directly by evaluation and scalar compatibility directly
from Mathlib's `smul_Spec_def`. No additional proof-dependency imports remain.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's original plan was valid but
unnecessarily demanded lifting differentials by fullness and unfolding coproduct
comparisons. Global sections and the already proved `freeSectionsEquiv_app` avoid both.
The unit `sk-thm-picard-perfect` and its cancellation route are preserved: this still
lifts the original complex and supplied unit coefficient, with no cancellation asserted.
The unit's `realized` record does not require any additional node-level route.

## Second reading by K2

1. Compared the delivered Lean module with the repository version. The theorem statement,
   declaration visibility, and existing imports are byte-for-byte unchanged; only the proof
   and private helpers changed.
2. Compiled the module with `lcompile.py` and checked that it contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof introduces no hollow data;
   its coordinate equivalences are explicit constructions. The resulting declarations use
   only the permitted foundational axioms (apart from any unrelated imported open proofs).
3. Checked the DAG and searched the library and recorded search results for duplicate
   statements. The sole target theorem is closed, no split-off statement was added, and the
   DAG proof steps and proof origin match the implemented global-sections argument.
4. Read the proof from the target downward. The global-sections route is shorter below the
   unit level and preserves the unit's required affine lifting route; all four imports remain
   necessary for the public statement or its proof. There are no prunable proof-dependency
   nodes or modules.
5. Checked the node metadata, including `proof`, `proof_deps`, `proof_origin`, chapter, and
   unit. They agree with the Lean proof, and the unit `sk-thm-picard-perfect` remains realized.

Changed only this report during second reading; no mathematical repair was needed.
