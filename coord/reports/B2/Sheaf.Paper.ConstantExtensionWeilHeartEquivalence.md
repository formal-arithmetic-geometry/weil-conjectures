## What changed

Filled five supporting theorem proofs in
`Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`, preserving every public signature,
definition body and public import. Added a private Mathlib finite-morphism import.
The field properties follow from the already proved unique-subfield theorem and
algebraicity in a scalar tower. The four model properties use finite field maps,
base change and composition. Sheet compatibility follows from the specified composite
of field inclusions. The fibre-map isomorphism is identified with the canonical
pullback-pasting isomorphism by its two projections. Closed images follow because
the projection is finite and hence closed. Scoped unused-section-variable linter
settings retain the original section binders.

## Proved and sorry left

Original holes: 9. Holes closed: 5. Holes added: 0. Split off: 0.

Closed, in namespace `WeilConjectures`:

- `constantExtensionField_properties`
- `constantExtensionModel_properties`
- `constantExtensionSheet_compatible`
- `constantExtensionFiberMap_isIso`
- `constantExtensionClosedImage_mem`

Remaining, all unchanged named theorem holes owned by
`lem-zl-constant-extension-weil-heart-equivalence`, with their original sources and
complete proof plans retained:

- `WeilConjectures.constantExtensionSheet_return`
- `WeilConjectures.constantExtensionCyclicSheets`
- `WeilConjectures.constantExtensionFiber_return`
- `WeilConjectures.constantExtensionWeilHeartEquivalence`

## No longer needed

None. The five supporting proofs follow their existing documented arguments.
Imports and dependencies for the unfinished main theorem are retained; no module
or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The main theorem and definitions its declared proof dependencies use share this
module. `ConstantExtensionSheetHeartCoordinates`, `ConstantExtensionPullbackReturnResidue`,
and `ConstantExtensionReturnLocalOperators` all publicly import this item. Directly
importing them here would create a cycle; the final assembly needs the definitions
separated first. This partial delivery closes five independent supporting holes.
No mathematical statement was corrected.

Two compile requests failed before Lean started with server temporary-directory
exhaustion (exit 125). The delivery checks subsequently reached Lean. Attempts at
the two Frobenius-return identities still had coercion issues and are not included.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
