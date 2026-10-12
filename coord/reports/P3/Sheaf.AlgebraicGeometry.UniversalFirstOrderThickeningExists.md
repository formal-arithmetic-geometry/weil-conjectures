## What changed

Copied the target module into the sandbox. Added the proof-only decomposition module `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExistence`, isolating the global existence conjunct. The target theorem now combines that existence statement with the existing uniqueness theorem `IsUniversalFirstOrderThickening.unique`.

## Proved and sorry left

The target theorem `FormallyUnramified.exists_universalFirstOrderThickening` is proved by a real constructor and application of `IsUniversalFirstOrderThickening.unique`. One strictly simpler intermediate theorem remains sorry: `FormallyUnramified.exists_universalFirstOrderThickening_existence`, the existence conjunct.

## No longer needed

No imports from the original target module were pruned; all are retained for the isolated existence proof's documented route.

## Where the brief, the DAG or earlier work was wrong

The seven-step global affine gluing proof is substantially larger than the available worker scope, so the existence conjunct was split into a strictly smaller named theorem. The uniqueness half is directly available from the existing definition module.

## New nodes

Added `lem-weil-pbc-universal-first-order-thickening-exists-existence` and its module declaration.

## Earlier second reading (a previous round; superseded)

The sandbox modules compile with `lcompile.py --all`; the target signature is unchanged. The added node records the strictly smaller existence conjunct and the target proof uses the existing uniqueness theorem.

## Second reading by P3

1. **Signatures unchanged.** Compared the delivered target module with the repository version: the existing target declaration has the same statement byte for byte; the only target change is its proof body. The added declaration is in a new module.
2. **Compilation and proof audit.** Compiled both sandbox modules with `lcompile.py --all`; they compile cleanly. The target theorem has no `sorry`; the only remaining `sorry` is the explicitly named split theorem `FormallyUnramified.exists_universalFirstOrderThickening_existence`, with its node. No forbidden declarations or hollow definitions were added.
3. **Split statement.** The added existence conjunct is a true strictly smaller result than the target and has a Stacks Project source, a complete proof description, and a matching DAG node. It is used to discharge exactly the existence conjunct; uniqueness is supplied by `IsUniversalFirstOrderThickening.unique`.
4. **Route and pruning.** The target proof follows the stated unit route: it invokes the split existence result and the existing uniqueness theorem. No imports or proof dependencies became unused, so none were pruned.
5. **DAG agreement.** The new node records the declaration, module, source, split status, proof origin, and dependency route. The unit realization remains unchanged; the target node's proof is reflected by the constructor plus uniqueness application.

Changed during second reading: added this review section only; no Lean declarations, statements, imports, or DAG data were altered.
