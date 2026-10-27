## What changed

Filled three proof bodies in `Sheaf.Paper.CompletedHomScalarTranspose` without changing
any declaration signature, definition, public import, or target.

* `ordinaryTransport_existsUnique`: use the inverse of the existing, proved
  `ordinaryScalarModelIso`, extend it termwise, transport its tensor-generator equation
  through its inverse, and prove uniqueness by `completedScalar_tensor_ext` in each degree.
  Private proof imports expose these existing proved helpers; no new data is chosen.
* `completed_conjugation`: expand the prescribed conjugation to the three completion
  isomorphisms, cancel the output comparison, combine the two Hom-functor maps, and
  cancel the two input comparisons.
* `derived_coherence`: specialize `scalarHomOrdinary_naturality`, the Hom clause of
  `scalarOperationsOrdinary_unit`, and the Hom clause of `scalarOperationsOrdinary_tower`.
  The naturality specialization explicitly uses preservation of the identity morphism.

The module remains a partial delivery, as allowed for an item with several holes.
Validation: the remote single-file compile passed in 18.8 seconds; its sole style
warning was removed before delivery. No target or public interface changed.

## Proved and sorry left

Closed 3 of the original 7 holes, all in namespace
`WeilConjectures.CompletedHomScalarTranspose`:

* `ordinaryTransport_existsUnique`.
* `completed_conjugation`.
* `derived_coherence`.

Added 0 holes; split off 0 statements. Four original named theorem holes remain,
all attached to `lem-pod-completed-hom-scalar-transpose`:

* `modelBaseChange_existsUnique`.
* `coefficientBaseChange_existsUnique`.
* `completed_hom_scalar_transpose`.
* `completion_implementation_transport`.

The coherence proof uses the existing unit and tower theorems, whose proofs remain
open in their own module. This delivery closes these three local holes; it does not
claim the resulting declarations have sorry-free transitive dependencies.

## No longer needed

Removed these unused private proof imports:

* `Sheaf.Algebra.Homology.PerfectDualScalarCalculus`.
* `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.
* `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`.
* `Sheaf.Algebra.Homology.OneKFlatChainTranspose`.
* `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
* `Sheaf.CategoryTheory.StrictRoosModel`.

These modules are not used by the three proofs delivered here. Their DAG nodes remain
in the plan for the four unfinished theorems; no node or module is withdrawn.
The four unfinished theorems retain their original DAG proof plan and dependencies;
no global pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

No statement error found. `completed_conjugation` needs only categorical cancellation
from the definition of `scalarHomCompleteInputs`; it does not need the stronger
`completion_implementation_transport` theorem. The derived coherence clauses are
already stated in the normalized scalar-operation API and can be specialized directly.
The ordinary model transport already exists as proved private helpers of
`IntegralScalarExtensionConstructible` and `FiniteFreeCompletedScalarComparison`.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
