## What changed

Added `GenericFormalFiberPurelyInseparableRegularAux` with two named intermediate theorems splitting the model disjunction into field and Cohen branches. The main theorem now unfolds the completion definition, introduces the finite purely inseparable extension, splits `hmodel`, and applies the corresponding intermediate theorem.

## Proved and sorry left

The main declaration `isRegular_genericFormalFiber_after_finite_purelyInseparable` is proved from the two branch declarations. The branch declarations `isRegular_genericFormalFiber_fieldModel` and `isRegular_genericFormalFiber_cohenModel` remain `sorry`, each with a node above.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG supplied no proof dependencies for the substantive regularity argument, so the unproved mathematical content was split into the two model branches required by the stated disjunction.

## New nodes

`new-lem-generic-formal-fibre-purely-inseparable-regular-field` and `new-lem-generic-formal-fibre-purely-inseparable-regular-cohen` record the two strict branch obligations.

## Second reading by U1

1. I compared the delivered main module with the repository version. The theorem signature is byte-for-byte unchanged; the only interface addition is the proof-only import of the auxiliary module. Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. They compile successfully. The only output is style linter warnings for local instance bindings. The two intentionally split branch theorems are the only remaining `sorry`s, and neither definition contains `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. Verdict: pass.
3. The split statements are the field-model and Cohen-model obligations from Proposition 07PS, strictly narrower than the parent disjunction and needed by its proof. Their source and DAG nodes are recorded. Verdict: pass.
4. The parent proof unfolds the completion, introduces the finite purely inseparable extension, splits the supplied model disjunction, and applies the corresponding branch theorem. This is the direct route and preserves the unit's model-branch route. No imports were removable. Verdict: pass.
5. The auxiliary declarations and the parent declaration agree with their DAG records; the parent node is realized by the existing theorem and the two branch nodes by the auxiliary module. Verdict: pass.

I changed only this report section. No Lean proof or statement required repair after compilation.
