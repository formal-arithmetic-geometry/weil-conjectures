## What changed

Proved `AlgebraicGeometry.locallyClosedClosureAdjointRealization` in
`Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization`, with every existing
declaration signature and definition unchanged. No source-library file was changed.

The proof constructs the Noetherian closure geometry and finite coefficients,
uses finite étale direct-image exactness and fixed-coefficient pro-étale closed
direct-image exactness, and obtains the étale comparison from the existing
locally closed extension comparison. For the pro-étale comparison it proves the
closure square Cartesian, applies the existing proper/open sheaf comparison,
and reflects the intrinsic comparison through the fixed-coefficient equivalences.
Both comparisons are normalized along restriction before passage to derived
categories. Constructible restriction uses the existing constructible pullback
theorem and the bridge between the two constructibility predicates. The chosen
adjoints satisfy the required lower bounds by the exact-derived-adjunction API;
the last two equations follow from the general conjugate-isomorphism identities.

Added only proved private helpers for these arguments, with no new public
declarations. Replaced the broad public coherence/adjoint imports with the
intrinsic finite-operations import needed by the existing public definitions.
Proof-only imports expose the actual proper/open comparison, fixed-coefficient
adjunction, constructibility bridge, finite exactness and Noetherian APIs.
Updated the existing node's proof, proof dependencies and proof origin to match.
No unit statement or unit proof route was bypassed.
Public-import exposure is documented in
`coord/changes/S8-locally-closed-closure-public-imports.md`.

Validation: the final module compiled without errors or warnings through
`lcompile.py` (10.0 seconds). The import-pruning check passed. No new modules,
definition changes, forced adaptations, or module withdrawals are included.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.locallyClosedClosureAdjointRealization`
(`lem-sf-locally-closed-closure-adjoint-realization`).

Holes added: 0. Holes remaining in the item: 0. Split-off statements: 0.
This is a complete proof from the library's existing declarations, including
existing proof dependencies that remain separate stage-3 items; it does not claim
those dependencies have already become axiom-free.

## No longer needed

Removed these original imports from this module:

- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient`:
  the published fixed-coefficient derived closed adjunction suffices.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`:
  the needed extension functors and adjoints are already supplied by their
  fixed-coefficient APIs.
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`:
  the actual pro-étale comparison comes from proper/open base change and a
  directly proved Cartesian closure square; normalization is proved locally.
- `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`:
  finite étale direct-image exactness and the existing closed ambient adjoint
  avoid reconstructing the supported-kernel equivalence.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`:
  exactness of the fixed-coefficient open and closed functors is already available.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  the intrinsic finite-operations equivalences provide the transport needed here.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  the needed inverse-image exactness is already present through the retained
  public APIs; no declaration from this private import is used directly.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`:
  the conclusion asks for lower-bounded comparison domains, which follow
  directly from exactness; no direct-image comparison theorem is required.

Removed obsolete top-level tool-use approvals from the item's node:
`lem-pur-etale-supported-kernel-adjunction`,
`lem-sfb-locally-closed-extension-coherence`,
`prop-weil-pbc-comparison-direct-image`, and
`prop-weil-pbc-proetale-constant-ring-map`.
Also removed the redundant proof-step dependencies
`def-weil-pbc-direct-image` and `def-weil-sheaf-of-modules-category`: the proof
uses the published exactness, adjunction and transport APIs directly instead of
reconstructing functors or module-sheaf categories from these definitions.
The updated numbered proof steps and their dependency union record the actual
replacement route. These are dependency-edge removals for this item, not claims
that the corresponding declarations can be deleted globally. No source-library
declaration was removed, and no other module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature repair was needed. The planned supported-kernel
construction and separate constant-ring comparison are unnecessary given the
existing finite-direct-image exactness and intrinsic finite-operations APIs.
The plan's last step describes applying direct-image comparison, whereas the
actual bundle field only records that both extension images stay bounded below.
That field follows immediately from exactness. The node and theorem's proof
description now specify the concrete comparison and exactness route used.
The first server preflight required a change record for public-import pruning;
that record is now included, with zero downstream Lean consumers and the retained
DAG parent documented. An earlier delivery attempt received no answer from the
busy compile server; it pushed nothing.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
