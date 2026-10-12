## What changed
Decomposed the parent theorem into two intermediate categorical obligations. The parent proof now composes the restricted comparison witness with the compatibility theorem. Added imports for both intermediate modules.

## Proved and sorry left
The parent declaration `AlgebraicGeometry.exists_canonicalModuleBaseChange_open_comparison` is proved by applying the two intermediate declarations. Sorry remains in `exists_restricted_module_pullback_comparison` (node `lem-pc-canonical-module-base-change-open-comparison-c0`) and `restricted_base_change_compatibility` (node `lem-pc-canonical-module-base-change-open-comparison-compat`).

## No longer needed
Removed the former proof-only imports `DerivedPullbackOpenRestrictionUniverses`, `DerivedDirectImageOpenRestriction`, `DerivedDirectImageCompositionUnbounded`, and `ModuleBaseChangeMapOpenRestriction`; the decomposed proof does not reference them directly.

## Where the brief, the DAG or earlier work was wrong
The DAG proof describes substantial derived categorical coherence but no existing Lean theorem provides it directly, so it was split into the two strictly smaller obligations above.

## New nodes
`lem-pc-canonical-module-base-change-open-comparison-c0` and `lem-pc-canonical-module-base-change-open-comparison-compat`.

## Second reading by K2

1. **Interface unchanged.** Compared the delivered parent module with the repository version: the theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof text differ.
2. **Compilation and proof audit.** Compiled all three sandbox modules with `lcompile.py --all`; there are no errors, no `axiom`/`unsafe`/`opaque` declarations, and the only remaining `sorry`s are the two explicitly named split theorems. The parent proof is a direct composition of those two witnesses.
3. **Split statements.** Checked both intermediate statements against the parent type. The first supplies exactly the restricted comparison witness; the second universally consumes that witness and supplies exactly the two restriction isomorphisms and compatibility equation. Both are strictly smaller obligations and retain the original hypotheses and conclusion strength.
4. **Pruning and route.** The unit route is retained through the parent theorem and its two decomposition obligations. The four former proof-only imports were unused after decomposition and were removed; the two intermediate theorem imports remain proof-only.
5. **DAG agreement.** The two node files name the delivered declarations and record the Stacks sources and decomposition route. No target or definition was changed.

Changed the parent module to scope the elevated heartbeat limit to its theorem (with a reason comment), removed four unused imports, and fixed the overlong C0 docstring line. No theorem statements or definitions were changed.
