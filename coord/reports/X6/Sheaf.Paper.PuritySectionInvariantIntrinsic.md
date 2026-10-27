## What changed

Completed `WeilConjectures.PurityFiniteSetting.sectionInvariantIntrinsic_invertible`
in `Sheaf.Paper.PuritySectionInvariantIntrinsic`, preserving every existing signature,
definition, instance, public import and docstring.

The proof constructs the finite index of nonempty smooth fibre-dimension loci and
applies `smooth_dimension_clopen_partition` and
`varyingDimension_finite_dualizing_inverse`. A private proved comparison identifies
the recorded exceptional functor with the finite-coefficient functor using
`Functor.mapDerivedCategoryCompIso`. Pullback preservation and the coefficient-unit
isomorphism give the pulled-back inverse. A private proved tensor comparison uses
uniqueness of the normalized K-flat tensor descent, not an arbitrary witness.
The two required isomorphisms are actual composites of this comparison, inverse
pullback tensor comparison, pullback of the two inverse maps, and the unit comparison.
A third private theorem transports the exact finite-Tor constructibility predicate
along an isomorphism.

Proof imports now name `VaryingDimensionDualizingInverse`, `AllStageCtfPullbackUnit`,
`FinitePullbackTensorComparison`, `CochainTensorModelRigidity`, and
`CohomologicalSmoothnessComparison`. The last supplies the already-proved
compactification wrapper. Elaboration options are scoped to the checked declarations.
The node's proof, proof dependencies and origin track this finite-level assembly.

The finite index is empty when V is empty; cover construction never chooses an
index without a point, and the assembly theorem explicitly includes that case.
For the identity section and dimension zero the same comparisons apply. No purity
orientation or constant relative-dimension hypothesis is added.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.PurityFiniteSetting.sectionInvariantIntrinsic_invertible`
(node `def-pur-section-invariant`). The other two existing theorems remain proved.
There are zero `sorry`s left in the item and zero holes added anywhere; zero split-offs.
The proof uses the existing declared dependencies, including their still-unproved
theorems; it does not claim their independent proofs.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.CohomologicalSmoothnessTheorem`
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.DerivedPullbackTensorIso`
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`
- `Sheaf.Paper.FiniteClopenExceptionalRestriction`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.PullbackTorAmplitude`

The section-invariant proof no longer needs
`lem-pur-derived-pullback-tensor-iso`: the ambient canonical finite tensor
comparison suffices for this finite-level theorem. Removed that dependency from
step 3, `proof_deps`, and the top-level `tool_uses` approval list. Its additional
all-stage tensor coherence declarations are not used directly here.

The clopen, cohomological-smoothness and pullback infrastructure remains reachable
through the retained varying-dimension and pullback dependencies; these modules
are not withdrawn or claimed globally prunable. The scalar-normalization and
finite-Tor site definitions also remain transitively imported. No declaration,
module or unit realization is deleted. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The DAG's tensor step names an all-stage
comparison; the existing finite-level declaration gives the needed part more
directly. The Lean realization needs two interface comparisons not written in
that abstract step: composition of derived site comparisons, and uniqueness of
the normalized derived tensor model. Both are proved privately from existing
library declarations. The proved tool `lem-sf-cochain-tensor-model-rigidity` is from unit
`sk-rem-sf-pf-done`; it supplies the uniqueness of the concrete tensor descent,
which the purity-conventions unit does not restate. The finite pullback tensor
comparison is within `sk-def-purity-conv`. No new nodes, statement repairs,
consumer adaptations or change records are needed.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
