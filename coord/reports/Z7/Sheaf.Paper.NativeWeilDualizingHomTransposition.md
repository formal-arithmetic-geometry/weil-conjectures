## What changed

Proved `AlgebraicGeometry.WeilComplex.native_dualizing_hom_transposition` in
`Sheaf.Paper.NativeWeilDualizingHomTransposition` without changing any existing
statement or definition. A proved private helper derives simultaneous source
naturality of inverse closed transposition from evaluation naturality and tensor
interchange. The main proof transports the existing dual-preservation theorem
along uniqueness of the supplied right adjoint, constructs the two actual Hom
bijections, and proves their formulas and all six naturality squares.

Updated the existing node's proof, proof dependencies and proof origin to match
the Lean argument. No source-library module was changed. The final module compiled through
`lcompile.py` in 24.2 seconds with exit code 0 and no warnings; the single-file
60-second limit and heartbeat limit were unchanged. All four existing definitions
and the theorem signature were checked against the shared source verbatim.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.WeilComplex.native_dualizing_hom_transposition`
(node `lem-sf-weil-dualizing-hom-transposition`). The item now contains zero
`sorry`s. No holes or new public declarations were added. This proves the item
from the existing stated dependencies; those dependencies retain their own
proof obligations, notably native tensor constructibility, native closed
comparison, and `objectProperty_derivedHom_dualizingComplex`.

## No longer needed

Removed proof imports `Sheaf.Paper.LocallyFiniteCoefficientRingRealization` and
`Sheaf.Paper.NativeModuleConstructibilityComparison`. Their nodes
`lem-sf-locally-finite-coefficient-ring-realization` and
`lem-sf-weil-verdier-module-constructibility-comparison` are no longer direct
proof dependencies of this item: the existing `NativeClosedComparison` already
provides the native derived-Hom model, and the existing native tensor-closure
and dual-preservation statements already apply to the exact object property.
Their mathematical comparisons may still be needed by those dependencies;
this delivery does not claim that these modules leave the targets' closure.

The public `NativeCompactProjectionFormula` import remains necessary for the
`nativeConstructibleTensor` definition used by the statement. Its projection
formula theorem is not used. No node or module is withdrawn; the unit's recorded
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's initial coefficient reconciliation step
is redundant at this assembly level. The supplied adjunction itself gives the
`HasUpperShriek` instance, so no additional adjoint-existence theorem is needed.
The proof uses the existing internal-Hom bifunctor and its native-model
isomorphisms to transfer constructibility between the two dualizing targets;
it assumes no equivalence with fixed pairs of ambient derived objects.

The sources checked were the current blueprint’s
`sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md`, Step 1, and
`fix-cor-verdier-exchange.proof.md`, Steps 1–2. No new statement requires
additional edge-case hypotheses: the private helper is valid in any closed
monoidal category with the recorded evaluation naturality, including zero or
identity input maps.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
