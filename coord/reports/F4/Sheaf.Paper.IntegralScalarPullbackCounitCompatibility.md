## What changed

Restored the quarantined item source at
`lean/Sheaf/Paper/IntegralScalarPullbackCounitCompatibility.lean` and proved
`WeilConjectures.integralScalarPullbackCounit_compatibility` with its entire
statement unchanged. The original public imports and all public signatures remain.
Added private proof imports of `ScalarExtensionTowerCoherence` and Mathlib's
adjunction uniqueness API, and two proved private helpers.

The supplied coefficient data extend to completed-operation models: retain an
auxiliary model's system tensor, transport its completion comparison by the
unique isomorphism of left adjoints to the same total-limit functor, and use C's
actual calculus, Roos models and pullback realizations. Mathlib's unit transport
equation proves the required completion-unit normalization. The existing tower
realization theorem supplies the unused tensor-side parameters, and the pullback
component of scalarExtensionTowerCoherence gives the desired equation. The last
step unfolds the counit wrappers and associates composition; completeness proofs
are identified by proof irrelevance.

Updated only the item's node proof, proof dependencies and proof origin to match.
No existing shared definition, statement or interface changes. No source-library
module is edited. Normalized completed-operation models are used as a generic
construction tool; this does not replace a step of the open-closed unit route.

## Proved and sorry left

Closed 1 of 1 existing holes:
`WeilConjectures.integralScalarPullbackCounit_compatibility`
(node `lem-sf-integral-scalar-pullback-counit-compatibility`).
Zero holes remain in the delivered module; zero holes added or split off.
The two private helpers are completely proved. The proof uses existing statements
`ScalarExtensionTower.realizationModels` and
`ScalarExtensionTower.scalarExtensionTowerCoherence`; their existing upstream
holes are unchanged and are not counted as newly proved by this delivery.

Validation: lcompile.py accepted the final module without warnings or errors in
13.6 seconds (60-second limit). Source comparison confirmed the public theorem
signature is unchanged, no Lean line exceeds 100 columns, and the delivered
module contains no sorry tokens.

## No longer needed

No original imports removed, and no module withdrawn or claimed globally pruned.
The direct proof dependency `lem-pc-kflat-resolution` and its explicit
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` import are not
needed here: the existing scalar tower theorem already packages the normalized
representative calculation. That node remains needed by the tower infrastructure.
Likewise `lem-pur-integral-operations-scalar-extension` is retained as a statement
dependency and public import but is not a separate proof step: its specified map
already occurs in the tower theorem's conclusion. The realization-model and
comparison-system definition dependencies remain. No new lemmas with holes were
introduced for representative calculations or counit compatibility.

## Where the brief, the DAG or earlier work was wrong

The item source was absent from lean/ and preserved in the quarantine path named
by coord/rework.tsv; restored it instead of interpreting that absence as withdrawal.
There is no current item-specific return entry for F4.

The earlier split report says that the scalar tower theorem's auxiliary
completed-operation and tensor models prevent its direct use for the supplied C.
Those parameters can in fact be supplied without changing C: uniqueness of left
adjoints transports the auxiliary completion comparison with its unit equation,
and realizationModels supplies the tensor models. Thus the representative-level
argument need not be reconstructed and no further split is necessary.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
