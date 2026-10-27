## What changed

Filled two theorem proofs in `Sheaf.Paper.CompletedHomScalarTranspose`.
`coefficientBaseChange_existsUnique` transports the existing scalar-extension unit
isomorphism to a complex concentrated in degree zero, proves the specified local
multiplication formula, and proves uniqueness by sheafified-tensor extensionality.
`completion_implementation_transport` identifies the strict chain maps by cancelling the canonical ordinary scalar
model isomorphism, constructs the derived ordinary transport
from the universal left-derived property, and proves the comparison square and
uniqueness by localization on good complexes.

Added only a proof import of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence`.
Reused the existing proof imports of `IntegralScalarExtensionConstructible` and
`FiniteFreeCompletedScalarComparison`. Updated the item's node proof and proof
dependencies to record these arguments. Existing signatures and definitions are
unchanged. In the unclaimed `IntegralScalarExtensionConstructible` module, the
already proved normalization calculation is factored into a proved private helper,
and another proved private lemma identifies the selected chain map with its explicit
model composite. No existing signature or definition body changes. The change record
is `coord/changes/G2-completed-scalar-chain-model-api.md`. A private definition caches the actual canonical cochain counit with
its named source and target functors. Proved private lemmas give its normalization
and universal property. Its fully typed model uses the canonical tower-derived instances. Local instance
priorities and irreducibility attributes remain confined to the proof sections.
The tensor model isomorphism also remains irreducible in its normalization lemma,
avoiding its large implementation term during uniqueness inference. A proved generic
unique-choice lemma supplies the selected-isomorphism equation. These proof interfaces
avoid repeated unfolding of the tensor and cochain model records.

## Proved and sorry left

Closed 2 of the original 4 holes, both in namespace
`WeilConjectures.CompletedHomScalarTranspose`:

- `coefficientBaseChange_existsUnique`.
- `completion_implementation_transport`.

Added 0 holes. The following 2 holes remain unchanged, both attached to
`lem-pod-completed-hom-scalar-transpose`:

- `WeilConjectures.CompletedHomScalarTranspose.modelBaseChange_existsUnique`.
- `WeilConjectures.CompletedHomScalarTranspose.completed_hom_scalar_transpose`.

The adapted `IntegralScalarExtensionConstructible` module retains its two existing
holes unchanged: `WeilConjectures.integralOrdinaryDerivedScalar_constructible` and
`WeilConjectures.integralConstructibleScalarComparison_existsUnique`. Thus the packet
contains four remaining holes in total; none is newly introduced.

The previously complete proofs of `ordinaryTransport_existsUnique`,
`completed_conjugation`, and `derived_coherence` are retained.

## No longer needed

None. No imports, declarations, nodes or modules are withdrawn. The dependencies
of the still-open main model calculation remain needed; their original plan is
retained in the node.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. Two steps previously described
as open can be discharged from the existing tensor-unit, single-complex and
universal-localization APIs. No arbitrary existence witness is used to define
new data, and no target statement or unit route changes.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
