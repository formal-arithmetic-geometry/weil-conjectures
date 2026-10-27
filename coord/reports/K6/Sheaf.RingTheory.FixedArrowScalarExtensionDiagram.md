## What changed

Proved `Module.fixedArrow_scalarExtension_diagram` in
`Sheaf.RingTheory.FixedArrowScalarExtensionDiagram`, without changing any existing
statement or definition. Added proved private helpers for scalar-extension comparison,
semilinear transition maps, their pure-tensor formulas and naturality, eventual equality,
and the additive colimit universal property.

The comparison maps use Mathlib `ModuleCat.extendScalarsComp`; transitions are the
scalar-extension unit followed by the comparison. Tensor induction proves coherence
and arrow naturality. Mathlib's finite-presentation tensor instance supplies stage
finite presentation. Finality of the upper-tail inclusion restricts the ring colimit.
The existing proved `Module.baseChange_diagram_elementwise` gives representatives
and eventual zero; their common-stage criterion constructs the additive colimit.
The DAG proof and dependencies have been updated to this implementation.

Validation: the full module compiles through lcompile.py with no warnings. Pure-tensor
proofs and the tensor finite-presentation instance impose no nonzero, flatness or
Noetherian conditions; the tail construction also covers a singleton index preorder.

## Proved and sorry left

Closed the one original hole: `Module.fixedArrow_scalarExtension_diagram`
(node `lem-trf-fixed-arrow-scalar-extension-diagram`). Added zero holes and split off
zero statements. No `sorry` remains in the delivered module. All private helpers
are proved. The public theorem has only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## No longer needed

Removed proof imports `Mathlib.LinearAlgebra.TensorProduct.RightExactness` and
`Mathlib.LinearAlgebra.TensorProduct.Pi`. Removed the planned direct dependencies
`lem-weil-pbc-tensor-right-exact` and `lem-weil-pbc-tensor-finite-product` from this
node's proof and tool-use list: Mathlib `instFinitePresentationTensorProduct`
already gives the required finite presentation, so this item needs no separate
presentation-matrix, right-exactness or finite-product argument. These Mathlib
results may remain transitive dependencies of the instance. No project module is
withdrawn, and no source-library declaration is removed. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition defect was found. The planned explicit comparison
inverse and finite free presentation calculations can be replaced by existing
Mathlib results. Tensor factors already use the elementwise theorem's ring-first
convention, so no tensor flip is required in the formal proof. No change record or
consumer adaptation is needed because all existing public interfaces are unchanged.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
