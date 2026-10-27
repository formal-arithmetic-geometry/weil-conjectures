## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_restrictedPush_acyclic` in the assigned module, with its statement and public imports unchanged. Both conjuncts use the existing continuous scalar-resolution theorem, transport through exact equivalences, and naturality/cancellation of the supplied derived unit after a K-injective resolution.

Added `Sheaf.Paper.DiagonalTraceRestrictionRingedModels`, proving `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_restriction_ringedModels`. It constructs the scalar map on the actual ringed sequence site, the constant-section/sequence equivalences, their comparison with every normalized `Restriction`, and the direct-image comparison. This is the presentation step alone: it mentions no complexes, K-injectivity or derived units. Its existential witnesses are explicitly constructed in its complete proof; no data are selected from an unproved existence theorem.

The item privately imports the new module, `CompactSupportScalarProofs`, `NativeConstantRestrictionAcyclicity`, `ProEtaleFixedScalarRestrictionDirectImage`, `ProEtaleRingSheafChangeAdjunction`, and `RingedStrictTowerHomotopyLimit`. The new module publicly imports `VaryingRingOperations` for the base-change functor in its signature, and privately imports the native and fixed-scalar modules for their proved presentation helpers. The arbitrary-ring constant-section equivalence is used for Z_l; no finite-ring theorem is applied to Z_l. All auxiliary definitions and instance attributes remain private or local.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_restrictedPush_acyclic` (node `lem-sfb-diagonal-trace-restricted-push-acyclic`). Also proved the new model-construction theorem `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_restriction_ringedModels` (node `lem-sfb-diagonal-trace-restriction-ringed-models`). Added zero holes. Neither delivered module contains `sorry`. Validated with `lcompile.py --all`: both delivered modules compiled without Lean errors. Temporary profiling instrumentation was removed before delivery.

## No longer needed

No original import is removed and no module is withdrawn. The planned dependency `det-sp-coefficient-towers-abelian` / `SmoothPurityCoefficientTowersAbelian` is unnecessary for this argument: `Systems` is already the actual sequence-site module category. Its node is removed from this item's direct proof dependencies; other consumers can still need it. The concrete scalar-map and presentation dependencies are retained under the new proved model-construction node. Ringed-topos composition and K-injective resolutions remain needed.

## Where the brief, the DAG or earlier work was wrong

The prescribed argument works without another unproved split. The existing proved generic helpers supply the sequence-site and constant-ring comparisons. `systemRing` reconstructs a sequence from adjacent transitions, so the scalar cone must target that reconstructed sequence. All five normalization fields of `Restriction` enter the concrete comparison.

The combined proof exceeded the per-file compile limit. We first used local irreducibility with proved projection equations for the constant-tower equivalence and factored the categorical isomorphism algebra. The remaining presentation construction is now a separate, fully proved module; the item consumes its models abstractly. No shared definition, existing statement, or downstream consumer is changed.

## New nodes

`lem-sfb-diagonal-trace-restriction-ringed-models`, in `dag/nodes/sec-six-functors-basics/`, realizes the concrete ringed presentation step from paragraph (1) of the current diagonal trace proof. Its new module is `Sheaf.Paper.DiagonalTraceRestrictionRingedModels`. The lemma is strictly the model-construction part of the argument and is proved completely. There are no change records or unproved split-off statements.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
