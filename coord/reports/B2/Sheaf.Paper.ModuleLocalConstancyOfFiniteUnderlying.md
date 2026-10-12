## What changed

Replaced the invalid target-restatement helper with an operation-lifting theorem that takes an
explicit underlying sheaf, its identification with the underlying module sheaf, and a specified
constant trivializing cover. The target theorem extracts that cover from the first conjunct of
`hF` and applies the helper. Both sandbox modules compile.

## Proved and sorry left

`AlgebraicGeometry.Scheme.module_localConstancy_of_finite_underlying` is proved by the real
constructor application in the module. Sorry remains only in
`AlgebraicGeometry.Scheme.module_operationCompatibleCover`, which is the finite-operation
refinement subargument and has node
`lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover`.

## No longer needed

Removed the unused public import `WeilConjectures.ConstructibleSheaf.Defs` from the helper module; the remaining public imports are required by its signature.

## Where the brief, the DAG or earlier work was wrong

The earlier helper had exactly the target conclusion from the same hypotheses and was therefore
only a renaming of the target. It has been replaced by a strictly smaller operation-lifting step
with an explicit cover and underlying sheaf identification.

## New nodes

`lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover` records the
operation-lifting statement and its Lean interface.

## Earlier second reading (a previous round; superseded)

The target module keeps its declaration unchanged and compiles. The helper has the strictly
stronger explicit inputs (underlying sheaf, identification, and chosen cover), so it is a proper
operation-lifting subargument rather than a restatement. The unit route still uses the finite
operation refinement step.


## Second reading by B2

1. Compared the delivered target module with the repository version. The target declaration and signature are byte-for-byte unchanged; only its proof and a private proof import changed. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`. The target has no `sorry`; the only remaining hole is the named `module_operationCompatibleCover` theorem. Axiom inspection shows only the permitted axioms together with `sorryAx` from that named split-off theorem. Verdict: pass.
3. Checked the split-off operation-lifting statement against its node and searched the library for duplicates. It is a strictly smaller theorem with explicit underlying sheaf, identification, and cover inputs, and its proof source and docstring are recorded. Verdict: pass.
4. The target proof uses the helper exactly as its DAG proof step specifies. The helper's unused `WeilConjectures.ConstructibleSheaf.Defs` import was removed; the remaining imports are required for the signature. Verdict: pass.
5. The unit record and target node retain the planned route through finite operation refinement; no unit statement or target statement changed. Verdict: pass.

Changed the helper import set and added the completed target proof. No new holes were added; one target hole was closed, while the previously named helper hole remains.
