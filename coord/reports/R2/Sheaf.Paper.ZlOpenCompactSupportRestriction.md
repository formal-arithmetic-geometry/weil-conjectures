## What changed

Proved `WeilConjectures.ZlOpenComplement.closedDomainFT` and
`WeilConjectures.ZlOpenComplement.closedDomainQC` in
`Sheaf.Paper.ZlOpenCompactSupportRestriction`. Rewrite the closed domain's
structure morphism using `Over.w i₀`, then use the existing closed-immersion
and composition instances for locally finite type and quasi-compact morphisms.
Both arguments apply to empty and nonreduced closed domains as well.

The inherited extra section parameters are preserved verbatim. Disable the
unused-section-variable linter locally for these two theorems; after replacing
sorry Lean correctly observes that the extra separatedness and other finite-type
parameters do not occur in the proof. No definition, signature, visibility,
public import or existing docstring changes.

## Proved and sorry left

Closed 2 of the module's original 3 holes:

- `WeilConjectures.ZlOpenComplement.closedDomainFT`.
- `WeilConjectures.ZlOpenComplement.closedDomainQC`.

One existing hole remains unchanged:

- `WeilConjectures.ZlOpenComplement.restrictionIdentities`
  (node `lem-zl-open-compact-support-restriction-identities`). Its existing
  docstring and DAG retain the complete argument and source.

Added 0 holes; split off 0 statements. This is a partial delivery of two
complete proofs, not a proof of the principal comparison theorem. Single-file
server compilation checked both helper proofs and the complete module.

## No longer needed

None. No imports removed and no nodes or modules withdrawn. The main theorem's
planned comparison dependencies remain needed by its unfinished proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. LeanFinder found only ordinary sheaf or
scheme-restriction results, not the required completed/rational/common-stage
comparison; Loogle and local source searches confirmed that the two closed-domain
helpers are direct consequences of existing Mathlib instances.

For continuing the main proof, the cited `integralOpenReductionComparison`
provides its Operations/TensorComparison/Comparison package, and
`integralPullback_completedComparison` provides the pullback Comparison.
`completedOpenExchangeComparison` supplies invertibility and completeness.
The remaining assembly must still identify the specified compact-support
functor, establish the empty-target zero comparison, and transport it through
raw rationalization and literal common stages, with arbitrary geometric-point
factorization. Existing `IntegralSupportNormalization.Normalization` supplies
support adjunctions and their disjointness relation; it does not directly
supply the full statement of `restrictionIdentities`. No new assertion or
extra hypothesis is introduced in this delivery.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
