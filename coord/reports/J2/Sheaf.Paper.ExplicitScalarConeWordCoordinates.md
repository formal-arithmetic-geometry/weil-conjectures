## What changed

Filled the remaining proof of
`WeilConjectures.ExplicitScalarCone.explicitScalarConeWordCoordinates`.
The proof transports the independently supplied normalized realization models
through the canonical comparison of reduction left adjoints, including their
actual intermediate counits. It then applies the existing completed scalar
pullback normalization in one simultaneous system and cancels the induced
whole-system isomorphism. The five previously proved supplemental statements
are unchanged.

Added proof imports of `PrimitiveQuotientRealizationsTransport`,
`IntegralScalarPullbackCompletionNormalization`, and
`AmbientComparisonSystemExistence`, all under `Sheaf.Paper`.
The primitive-model transport helper is fully proved in its own new module;
its four construction/evaluation helpers and the item-local helpers are private
and proved. The two private model-transport definitions are
marked irreducible to keep elaboration from repeatedly expanding their large
normalization fields; their realization equations are explicitly unfolded where
needed. Debug profiling options and the temporary diagnostic module are removed.
The new proof sections use `respectTransparency = true`, with imported large
functors locally irreducible. The main section restores the original environment
before the supplementary proofs. Existing public signatures, definitions,
attributes and public imports stay unchanged. The item's DAG
proof now records this route.

## Proved and sorry left

Closed the one remaining hole:
`WeilConjectures.ExplicitScalarCone.explicitScalarConeWordCoordinates`
(node `lem-pod-explicit-scalar-cone-word-coordinates`).

Initial item holes: 1. Final item holes: 0. New holes: 0. Split off obligations: 0.
The new theorem
`WeilConjectures.PrimitiveReductionTransport.realizations_transport`
(node `lem-pod-primitive-quotient-realizations-transport`) is fully proved,
with zero holes in its module.
The proof uses existing declared dependencies, including the existing
`ambientComparisonSystem_exists`; their proofs are separate stage-3 items.

## No longer needed

No existing Lean import is removed in this delivery; all three added imports
are used. No module is withdrawn. The direct proof dependencies below belonged
to the former ten-step plan and are no longer needed directly by this node;
some remain transitive dependencies of the reused normalization theorem.

- `lem-weil-isomorphism-scalar-tensor-kflat-model`
- `lem-pur-kflat-change-of-rings`
- `lem-trf-ringed-kflat-word-comparison-descent`
- `lem-pur-coefficient-extension-reduction-model`
- `lem-weil-isomorphism-derived-pullback-comparison-normalization`
- `lem-weil-finite-free-completed-scalar-comparison`
- `lem-trf-completion-unit-strict-quotient-model`
- `lem-weil-strict-roos-comparison`
- `lem-weil-isomorphism-comparison-natural`
- `lem-trf-sequence-scalar-generator-interchange`
- `lem-weil-isomorphism-scalar-augmentation-cone`

The existing supplemental generator and cone proofs still use their recorded
strict-cone, quotient-section and Roos dependencies. The unit statement and
its finiteness route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original ten-step proof is unnecessary as a new calculation: the library
already states and proves completed scalar pullback normalization in a
simultaneous comparison system. It does not immediately cover the separately
supplied primitive models of this item. The new proof supplies that missing
transport explicitly, using primitive uniqueness and the actual adjunction
unit/counit comparison equations. In particular it does not replace a counit
by an arbitrary reduction isomorphism or infer derived equality from separate
finite evaluations.


The finite intrinsic adjunction node contained an incorrect bundled citation:
`def-sp-finite-intrinsic-direct-adjunction` named
`def-weil-derived-direct-image` (including integral and common-stage operations)
for its finite uncompleted K-injective construction. Its actual Lean source uses
`proEtaleConstantDerivedDirectImage`, whose docstring explicitly names
`def-weil-pbc-proetale-operations`. This delivery corrects that citation in the
statement and proof metadata, records that all existing citing statements still
hold, and changes no Lean code in that module. With this correction the reused
normalization has no dependency path back to this item. See
`coord/changes/J2-finite-intrinsic-direct-image-citation.md`.


## New nodes

`lem-pod-primitive-quotient-realizations-transport`, in
`lean/Sheaf/Paper/PrimitiveQuotientRealizationsTransport.lean`, proves the
reduction-calculus transport of both normalized primitive realization models.
It constructs the transported models, proves their normalization and applies the
existing primitive uniqueness theorem. This is a strict part of the argument:
it involves no scalar/pullback interchange, explicit cone comparison or
constructibility, and the item still proves their composite word equation.
The monolithic proof exceeded 60 seconds after local irreducibility improvements;
this self-contained, fully proved subargument is compiled separately. No hole
is moved or added. The existing-node citation correction is recorded at
`coord/changes/J2-finite-intrinsic-direct-image-citation.md`.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
