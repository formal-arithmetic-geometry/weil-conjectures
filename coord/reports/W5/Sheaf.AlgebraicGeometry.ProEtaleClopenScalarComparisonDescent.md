## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_comparison_descent`
with its original signature. Its ordinary comparison comes from the new, proved
`Sheaf.AlgebraicGeometry.ProEtaleClopenOrdinaryScalarComparison` module. This module
constructs the original change-of-rings tensor-presheaf comparison explicitly and
uses the existing restriction/sheafification isomorphism. It proves the formula on
pure tensors and transports it through the prescribed presentation equalities.

The item applies this comparison degreewise. A private one-variable resolving
representative argument gives full faithfulness of restriction of natural
transformations. The two normalized computation maps then descend the comparison
as an isomorphism. Cancellation and that faithfulness give the representative
square and uniqueness for arbitrary competing natural transformations.

All added imports in the item are private proof imports. Its public import and
all existing declaration signatures stay unchanged. The new module publicly
imports only the existing scalar-comparison data needed by its statement.
The ordinary proof keeps pushforward abstract while proving naturality and restores
its sectionwise transparency for the tensor formula; this brings the full file
under the required time limit. No source-library files or consumer modules change. The item's node now records
the actual proof route. The unit's realized statement/steps are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_comparison_descent`
(node `lem-pur-clopen-scalar-comparison-descent`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_ordinary_scalar_comparison`
(node `lem-pur-clopen-ordinary-scalar-comparison`). All private helpers are proved.
There are zero remaining holes in either delivered Lean module and zero added
holes. This is a proof of the assigned hole, not a decomposition into new holes.
Existing imported mathematical obligations retain their own original proofs and
hole status. The final import-ordered server compile passed without warnings:
ordinary comparison 56.0 seconds, assigned descent 34.1 seconds. The derived
helper and assembly scratch checks also passed and were removed before delivery.

## No longer needed

No existing public import was removed, and no Lean module is withdrawn.
The item no longer needs the planned proof dependency
`lem-pur-clopen-scalar-model-properties`
(`Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarModels`): it uses the given
normalizations' computation-isomorphism fields directly instead of requiring an
already constructed comparison to invoke the model-properties theorem.

The item also no longer needs the planned binary tensor-descent dependency
`lem-weil-pbc-site-derived-tensor-descent`
(`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`).
One-variable resolving-representative localization suffices for the two scalar
functors. These are removed dependency edges of this node, not assertions that
those modules have no other consumers. The localization universal property,
exact clopen restriction, and underlying sheaf tensor remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The original plan's scalar-model-properties
lemma assumes a comparison, so it does not itself construct the comparison
requested here. Direct use of `Normalization.computed` supplies that step without
circularity. The available generic scalar restriction comparison uses
`changeOfRingsOfUniverses`; the presentations in this item use the original
`changeOfRings`. The delivery reuses the generic restriction/sheafification proof
and proves the short original tensor-presheaf bridge rather than identifying the
two constructions without proof.

The current unit record has empty realized statement/step lists. The latest
blueprint places `sk-def-purity-conv/_section.md` under `sec-six-functors-basics`,
rather than the older chapter path in the unit record. The latest unit text and
section-invariant definition were read; no unit statement or route was bypassed.

## New nodes

`lem-pur-clopen-ordinary-scalar-comparison` records the proved ordinary comparison
in `Sheaf.AlgebraicGeometry.ProEtaleClopenOrdinaryScalarComparison`. It is strictly
the ordinary, pure-tensor portion of the assigned argument, with no derived
comparison or uniqueness assertion. It needs only an open immersion, so includes
empty components and zero coefficient rings. Its node records the source,
explicit proof steps, searches, and exact Lean signature. No change record is
needed: no existing definition or statement changes.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
