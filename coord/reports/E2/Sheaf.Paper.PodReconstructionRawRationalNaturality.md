## What changed

Proved `WeilConjectures.PodRawReconstruction.reconstructionRawRationalNaturality`
without changing its statement or the realization predicates. The actual adjunction
unit restricts reconstruction to the full integral constructible category. Its tensor
extension defines the raw rational functor, and tensor induction proves naturality
on every rational arrow. The scalar comparison is the conjugate of the two actual
units; the inverse-unit equation uniquely characterizes it, including for ramified
coefficient extensions. The component calculation uses the recorded rational scalar
extension on integral arrows and preserves both endpoint transports explicitly.

Ambient integral linearity uses the already proved strict-system restriction and
limit linearity from CompactSupportReductionTower. Adjoint linearity gives reduction
linearity. The existing normalizedDerivedLinear comparison identifies the action with
the published integral constant-section action.

## Proved and sorry left

Closed one original hole: `WeilConjectures.PodRawReconstruction.reconstructionRawRationalNaturality`.
The original hole `WeilConjectures.PodRawReconstruction.reconstruction_identityCompactSupport`
remains, attached to `lem-pod-reconstruction-raw-rational-naturality` with its unchanged
complete proof plan. No holes are added. This is one proof out of two original holes.

## No longer needed

The first theorem no longer needs the identity-coefficient scalar-extension/Roos
comparison route or a separate same-index completion scalar comparison: linearity
comes from the limit adjunction, and the scalar comparison is uniquely prescribed
by the actual unit isomorphisms. The second theorem retains its original strict
identity-tower route and all its DAG dependencies. No module is withdrawn.

Removed unused proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.CategoryTheory.StrictRoosComparison`,
`Sheaf.CategoryTheory.SemilinearScalarLocalization`, and
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
The public statement imports are preserved. The other original proof imports
provide the finite-identity definitions and the remaining identity-tower statement.

Proof dependencies no longer used by either retained proof route:
`lem-weil-integral-scalar-extension-well-defined`,
`lem-trf-completion-unit-strict-quotient-model`,
`lem-weil-proetale-countable-products-exact`, `lem-weil-strict-roos-comparison`,
`lem-pur-semilinear-scalar-localization`,
`lem-weil-integral-scalar-extension-constructible`, and
`lem-pod-completion-unit-scalar-intertwining`. Their definitions may remain visible
through statement imports; this list concerns direct proof use, not a claim that
these modules have no other consumers.

The corresponding obsolete top-level `tool_uses` approvals are removed, preserving
the order of the remaining approvals. No approvals are added.

Added proof dependencies are the already proved completeness comparison,
constructible isomorphism closure, and the compact-support representative-independence
normalization lemma. They preserve the unit route and only identify existing scalar
structures or predicates.

## Where the brief, the DAG or earlier work was wrong

The unrestricted completeness predicate uses an auxiliary finite-field datum in
universe zero. The given datum is in universe u, so it cannot be inserted directly.
The proof constructs the prime-field datum with the same characteristic in universe
zero, and applies the proved intrinsic/legacy completeness equivalence to it.
No target or other declaration statement is changed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
