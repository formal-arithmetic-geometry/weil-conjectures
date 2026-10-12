## What changed

Proved `moduleOverFunctor_additive_proof` and `moduleOverMap_additive_proof` by constructing `Functor.Additive` and reducing map addition definitionally (`rfl`). Their corresponding instances compile unchanged.

## Proved and sorry left

Proved: `moduleOverFunctor_additive_proof`, `moduleOverMap_additive_proof`.

Sorries remain in `moduleOverFunctor_limits_proof`, `moduleOverFunctor_colimits_proof`, `moduleOverMap_limits_proof`, `moduleOverMap_colimits_proof`, and `derived_hom_mayer_vietoris`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

No errors found.

## New nodes

None.

## Second reading by S1

1. **Statements unchanged.** Compared `lean/Sheaf/Paper/DerivedHomMayerVietoris.lean` with the repository version. All declaration signatures and definitions are byte-for-byte unchanged; no change record is needed. Verdict: pass.

2. **Proof validity.** Compiled the module with `lcompile.py`; it compiles cleanly. The two additive proof theorems are closed by explicit `Functor.Additive.mk` constructions reducing map addition by `rfl`. Remaining five theorem sorries are exactly the named split-off declarations listed above; there are no sorries in definitions, axioms, unsafe, opaque, extern, or implemented_by declarations. Verdict: pass.

3. **Split-off statements.** No new statements or nodes were added. Existing split-off declarations are documented in the source and correspond to the existing DAG node. The additive proofs do not duplicate any upstream theorem. Verdict: pass.

4. **Pruning and route.** The proof uses only the existing imports and does not introduce a shorter route that bypasses a unit step. No imports or proof dependencies became unused, so `No longer needed` remains `None`. Verdict: pass.

5. **DAG agreement.** The proof fields for the two closed declarations now match the Lean proofs; all remaining declarations retain their prior proof status and dependencies. The unit route and realized fields are unchanged. Verdict: pass.

Changed only the proofs of `moduleOverFunctor_additive_proof` and `moduleOverMap_additive_proof`; no statements, definitions, imports, or DAG nodes were changed.
