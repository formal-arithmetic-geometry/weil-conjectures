## What changed

Added the affine-local intermediate theorem
`higherDirectImage_isQuasicoherent_on_affines` (left as a named theorem for the ordinary
higher-image comparison), then proved `isQuasicoherent_higherDirectImage` from it using
`SheafOfModules.IsQuasicoherent.of_coversTop` and the affine-open cover of the base.

## Proved and sorry left

Closed `isQuasicoherent_higherDirectImage`. Added one named sorry,
`higherDirectImage_isQuasicoherent_on_affines`, recorded as node
`new-higher-direct-image-affine-local-qcoherent`.

## No longer needed

The attempted ordinary-theorem import was removed because it creates an import cycle through the
proper-flat modules. No existing proof dependency node is otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The direct ordinary-theorem route is cyclic in this module. The proof is therefore reduced to the
strictly smaller affine-local statement and a real local-to-global proof.

## New nodes

`new-higher-direct-image-affine-local-qcoherent`: affine restrictions are quasi-coherent; its
proof is the affine localization and ordinary right-derived comparison from Stacks Tag 01XJ.

## Earlier second reading (a previous round; superseded)

The affine-local declaration is local in form, but equivalent to the target by locality and its docstring records the
Stacks source and blueprint node. The target is unchanged and is obtained by the genuine affine
cover criterion; only the affine comparison remains open.

## Second reading by K2

1. **Visible changes and statements.** I compared the delivered module with the repository version. Existing declaration signatures and definitions are unchanged. The only new declaration is `higherDirectImage_isQuasicoherent_on_affines`, whose statement is an affine-local step used by the target proof; the target statement remains byte-for-byte unchanged.

2. **Compilation and proof status.** The module compiles with `lcompile.py`. There are no prohibited declarations or `sorry` in definitions. The sole remaining `sorry` is the named theorem `higherDirectImage_isQuasicoherent_on_affines`, matching node `new-higher-direct-image-affine-local-qcoherent`; the target theorem `isQuasicoherent_higherDirectImage` is now proved by the affine-open cover criterion.

3. **New statement and dependencies.** I checked the new node against its Lean declaration and source citation (Stacks Tag 01XJ). Its hypotheses and conclusion are true, but the quantified affine-local assertion is equivalent to the target by locality, and its DAG `statement`, `proof`, `proof_deps`, `proof_origin`, `lean`, chapter, and unit fields agree with the code. The ordinary higher-image theorem remains the stated unresolved dependency rather than being duplicated here.

4. **Shortest route and pruning.** The proof uses `SheafOfModules.IsQuasicoherent.of_coversTop` together with `iSup_affineOpens_eq_top`; this is the direct local-to-global route available in the imported library. No proof-only import became unnecessary, and no existing proof dependency node or module was pruned. The added affine-local step keeps the intended coherence-unit route.

5. **Axiom and edge-case review.** Compilation passed, but a separate `#print axioms` scratch check has not yet been completed. The cover argument also handles the empty and affine-base cases through the existing affine-open supremum and criterion.

I removed extraneous blueprint comments that had been inserted into the unrelated local-vanishing declarations. No mathematical statements or imports were changed beyond the affine-local split and the target proof.

Delivery dry run could not reach preflight: `git fetch -q origin` failed because SSH to the project server port 22 timed out. The affine-local split remains a candidate decomposition, not a certified strict reduction; its equivalence by locality must be resolved before delivery. One upper hole is closed and one lower hole added, so net holes closed is zero.
