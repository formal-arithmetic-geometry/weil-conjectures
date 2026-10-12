## What changed

Added the intermediate theorem `formalModuleQuotient_factor` expressing the affine ideal-power inclusion and factorization needed for quotient reduction. Used it to prove `formalModuleQuotient_map_zero`; all other imports and declarations are unchanged.

## Proved and sorry left

Proved `formalModuleQuotient_map_zero`. Sorries remain in `formalModuleQuotient_factor` (new node `lem-weil-pbc-formal-module-ideal-power-factor`), `formalCompletionSystem_coherent`, and `formalModule_annihilated_power_iff`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted the explicit factorization theorem required to express the ideal-power inclusion in Lean's categorical language; it is added as a strictly simpler intermediate statement.

## New nodes

`lem-weil-pbc-formal-module-ideal-power-factor` records the factorization theorem and its source argument.

## Earlier second reading (a previous round; superseded)

The reduction proof is compiled in the sandbox; the new factorization statement is strictly simpler than the closed theorem and is exactly the missing categorical step.

## Second reading by V3

1. Compared the delivered module with the repository version. Existing declaration signatures and definitions are unchanged; only the new intermediate theorem and the proof of `formalModuleQuotient_map_zero` differ.
2. Compiled `lean/Sheaf/AlgebraicGeometry/CoherentFormalModule.lean` with `lcompile.py`; it compiles cleanly. The remaining `sorry`s are exactly the named declarations reported above, and no prohibited declarations or hollow definitions were introduced.
3. Checked the new factorization statement against the ideal-power inclusion argument and its DAG node. It is a true, strictly simpler intermediate result needed by the reduction proof; no existing library theorem duplicates it.
4. The proof uses the stated factorization route and preserves the unit route. No imports or proof dependencies can be pruned from the delivered proof.
5. The DAG node for `formalModuleQuotient_factor` matches its Lean declaration, source, proof description, and dependency. No other node metadata is changed.

Changed only the proof of `formalModuleQuotient_map_zero`, adding the split-off `formalModuleQuotient_factor` theorem and its node; no existing target statement was changed.
