## What changed

Replaced the body of `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_coherence`
with an assembly proof preserving its complete statement. Added the proof-only import
`Sheaf.Paper.NativeWeilTensorConstraintLifts`. No existing public import or interface changed.

The private, category-independent `assemble_tensor_constraints` derives the monoidal laws
using Mathlib `Monoidal.induced` through a faithful model functor. It derives braiding
naturality and both hexagons using `BraidedCategory.ofFaithful`, and proves involutivity
by mapping the double swap and cancelling the model tensorator. The tensor functor is
literally the supplied `T`, including its map on pairs of arrows. Forgetting is not
assumed faithful. Its associativity square comes from the constructed `CoreMonoidal`
oplax structure; its unit squares come from the individual inducing equations; its
symmetry square and exact coefficient-unit equation use the prescribed comparisons.

The new module states the remaining geometric lifting problem for individual constraints.
Its raw `TensorConstraintCandidate` has no naturality or coherence axioms. Its genuine
operations definition uses `T.map` and the fixed coefficient unit. `TensorConstraintLifts`
records the raw comparison diagrams in a faithful symmetric model and under forgetting.
The new theorem does not assert that these operations form a monoidal or braided category:
the parent proof establishes those laws. This separates the action-site and representative
identification work from the now-proved coherence verification.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_coherence` (1 of 1).
The private `assemble_tensor_constraints` is complete.

Validation: remote `lcompile.py` compiled the new raw-data module, then compiled the
original item against it without errors or warnings (reported 6.4 seconds for the
final item check). A local text comparison confirms that the original theorem
statement is verbatim unchanged. Both node proof-dependency lists equal the union
of their proof steps’ uses; both Lean files have lines of at most 100 characters.

Added one hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_constraint_lifts`, node
`lem-sf-native-weil-tensor-constraint-lifts`, in its own new module. Its entire proof
is `by sorry`; its docstring and node state the action-site construction and all
representative and normalization steps. No definition contains a hole and no
object is defined by choosing an arbitrary witness of this theorem.

This is a decomposition, not a net hole closure: one upper hole closed and one
strict constraint-lifting obligation added. It removes verification of the monoidal
and braiding axioms from the remaining obligation, rather than renaming the original
existential monoidal-coherence result. The actual construction of the candidate
isomorphisms and their model/forgetful images remains unfinished.

Edge cases checked in the formulation: zero objects, the empty site, characteristic
two, arbitrary negative degrees and unbounded complexes require no extra hypothesis.
The formal assembly is valid for arbitrary categories, including empty ones when its
specified unit data exists. No faithfulness claim about derived forgetting is used.

## No longer needed

None. No public import was removed and no module was withdrawn. The three original
proof dependencies (`lem-sf-weil-frobenius-action-resolutions`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`, and
`lem-sf-ringed-forget-tensor-descent`) remain dependencies of the geometric lifting
node. The parent now depends on that node and uses Mathlib for the formal laws.
No original dependency is claimed pruned merely because its use moved to the new node.

## Where the brief, the DAG or earlier work was wrong

No statement correction or source-library adaptation. The DAG plan described the
constraint conjugation and law verification together. The new split makes the raw
lifting data explicit and verifies the coherence laws with existing Mathlib theorems.
The native forgetful functor need not be faithful on derived morphisms; the proof
uses a separate faithful realization into a transported ringed model instead.

The source `PrescribedTensor` already proves transport of a known monoidal tensor through
a bifunctor isomorphism. It does not supply the native geometric constraints or their
images for the specified mate; our assembly uses Mathlib faithful induction directly
for the raw constraints, with the fixed literal coefficient unit.

The searched `NormalizedTensorConstraintTransport` concerns completed coefficient
systems and Roos limits, not native Weil constraints, and is not a duplicate.
The unit route is preserved; no unit or chapter record changed.

## New nodes

`lem-sf-native-weil-tensor-constraint-lifts`, module
`Sheaf.Paper.NativeWeilTensorConstraintLifts`: individual associator, unitors and
signed swap with raw inducing equations in a faithful model and under the fixed
forgetful tensor comparison. Its statement, proof in words, source, searches,
blueprint ancestry and Lean attachment are included. The native theorem is its
single remaining hole. No change record is needed: existing interfaces are unchanged.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
