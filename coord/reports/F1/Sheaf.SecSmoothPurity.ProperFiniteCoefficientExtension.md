## What changed

Added the proof-only module `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore`, which packages the first two clauses of the assigned theorem as a named intermediate result. The assigned module now imports this core and proves the final mate normalization by adjunction injectivity and `mateEquiv_counit`.

## Proved and sorry left

The final normalization clause of `properFiniteCoefficientExtension` is proved. The first two clauses are reduced to the new theorem `properFiniteCoefficientExtensionCore`, whose proof remains `sorry` and is recorded by node `lem-asd-proper-finite-coefficient-extension-core`. One original sorry was closed; one strictly smaller intermediate theorem with one sorry was added.

## No longer needed

The parent module no longer needs its former direct imports: the projection, tensor/pullback,
restriction/direct-image, derived-change-of-rings and K-flat modules are consolidated behind
`Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore`. They remain imported by that core
module because its statement and eventual proof use them. No declared proof dependency below the
core theorem was pruned.
The interface change is recorded in
`coord/changes/proper-finite-coefficient-extension-imports.md`.

## Where the brief, the DAG or earlier work was wrong

The DAG plan correctly identifies the unbounded scalar mate and the proper projection comparison, but the available declarations do not expose the full K-flat descent and conservativity argument as a single proved theorem. The proof was therefore split at the genuine comparison result, while the canonical mate normalization was completed directly.

## New nodes

`lem-asd-proper-finite-coefficient-extension-core` records the strictly smaller isomorphism and restricted projection clauses, sourced from Stacks Tag 0GL6 with the counit and composition normalizations of Tags 0B56 and 0D6E.

## Second reading by F1

The parent normalization proof and core split were reread against their signatures. Both
sandbox modules compile, and the core node's `lean.statement` is generated verbatim from its
theorem declaration.
