## What changed

In `Sheaf.Algebra.Homology.PerfectTensorRoosCompletion`, completed the proofs of
`CochainComplex.PerfectTensorRoos.scalarQuotientIso_existsUnique` and
`CochainComplex.PerfectTensorRoos.scalar_extension` without changing their statements.

The first proof constructs the degreewise quotient/base-change isomorphism using
Mathlib's `TensorProduct.tensorQuotMapSMulEquivTensorQuot`, transports the ideal-power
identity, checks the differential on scalar tensors, and proves uniqueness by
cancelling the surjective extended quotient map. Two private helpers with complete proofs keep
this computation local.

The second proof uses the source library's finite-projective preservation-of-limits
lemma. The canonical product map factors as `piComparison` followed by the product
of the levelwise quotient isomorphisms. The prescribed two cone coordinates imply
invertibility of the scalar Roos comparison. Those same coordinates and the quotient
projection equations prove the augmentation square. Strict augmentation naturality
then proves the balanced tensorator square.

Added only private proof imports for tensor/quotient equivalences, preservation of
products, and finite-projective scalar extension. Updated DAG step 10 and proof_origin
to record these implementations. The route and the unit statement are unchanged.
The quotient construction works for arbitrary ring maps and ideals, including the
zero ring, zero ideal, unit ideal, and zero module. The finite-free proof uses no
boundedness or projectivity hypothesis on the two complex models.

## Proved and sorry left

Closed two of the six original holes:

- `CochainComplex.PerfectTensorRoos.scalarQuotientIso_existsUnique`.
- `CochainComplex.PerfectTensorRoos.scalar_extension`.

Added no holes and no split-off statements. Four original holes remain, all attached
to `lem-sf-perfect-tensor-roos-completion`:

- `CochainComplex.PerfectTensorRoos.perfect_tensor_roos_completion`.
- `CochainComplex.PerfectTensorRoos.derived_completion`.
- `CochainComplex.PerfectTensorRoos.ramified_extension`.
- `CochainComplex.PerfectTensorRoos.scalar_identity_composition`.

## No longer needed

No imports, modules, or DAG dependencies are withdrawn in this partial delivery.
The unfinished parts still retain the original dependency plan. No new dependency
on a holed theorem was introduced by the completed scalar proofs.

## Where the brief, the DAG or earlier work was wrong

Both completed declarations were checked with `#print axioms`; each uses only
`propext`, `Classical.choice`, and `Quot.sound`. Diagnostic commands were removed
from the submitted file. A profiler run compiled the full file in 48.4 seconds.

No mathematical statement correction was needed. The scalar-extension portion of
step 10 can be proved directly using the existing finite-projective module limit
preservation API and the explicit coordinates already supplied by this module.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
