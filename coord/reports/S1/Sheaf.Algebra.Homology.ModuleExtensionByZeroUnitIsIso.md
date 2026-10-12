## What changed
Proved `moduleExtensionByZero_unit_isIso` by reducing it to monomorphism and epimorphism of the unit and applying balancedness of module sheaves. Added the intermediate declarations `moduleExtensionByZero_unit_mono` and `moduleExtensionByZero_unit_epi`, each as a named theorem for the remaining direct-sum argument.

## Proved and sorry left
The target theorem `moduleExtensionByZero_unit_isIso` is proved. `moduleExtensionByZero_unit_mono` remains sorry (node `lem-sc-module-extension-by-zero-unit-mono`), and `moduleExtensionByZero_unit_epi` remains sorry (node `lem-sc-module-extension-by-zero-unit-epi`).

## No longer needed
None; the imported open restriction adjunction theorem remains needed by all three declarations.

## Where the brief, the DAG or earlier work was wrong
The planned direct proof is substantial; the proof was decomposed into the strictly simpler mono and epi properties and combined using the balanced category structure.

## New nodes
`lem-sc-module-extension-by-zero-unit-mono` and `lem-sc-module-extension-by-zero-unit-epi` record the two intermediate obligations.

## Second reading by S1

1. The delivered module preserves the target theorem signature byte for byte; the proof only supplies `Mono` and `Epi` instances for the unit and invokes `isIso_of_mono_of_epi`. Verdict: pass.
2. All three delivered modules compile with `lcompile.py --all`; the only diagnostics are style warnings for proposition-valued `haveI`, and no declaration contains forbidden constructs. The two split declarations retain documented `sorry`s with matching DAG nodes. Verdict: pass.
3. The split statements are the strictly simpler monomorphism and epimorphism obligations, both true consequences of the direct-sum extension-by-zero argument and each needed by the target proof. No duplicate library declaration was found. Verdict: pass.
4. The target node proof and dependencies were updated to match the actual mono/epi route; no imports can be removed without losing those declarations. The unit's exact-adjunction route remains imported and the unit record is unchanged. Verdict: pass.
5. DAG and Lean declarations agree, including the two new split nodes and the target proof dependencies. Verdict: pass.

Changed the target node proof metadata and added this second-reading record. The linter change is recorded in coord/changes/moduleExtensionByZero_unit_isIso.md. No Lean proof text required repair.
