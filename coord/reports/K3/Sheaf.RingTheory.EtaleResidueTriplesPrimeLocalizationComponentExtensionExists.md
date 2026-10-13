## What changed
Added the auxiliary affine-model/factorization theorem module and used it to prove `etaleResidueTriples_primeLocalization_component_extension_exists` by composing the extension equation with cocone naturality.

## Proved and sorry left
The target theorem is proved. The auxiliary theorem `etaleResidueTriples_primeLocalization_component_extension_aux` remains `sorry`, recording the finite-presentation descent and localization argument.

## No longer needed
The original unimplemented proof dependencies are pruned from the target proof and replaced by the auxiliary theorem.

## Where the brief, the DAG or earlier work was wrong
The original DAG proof expands a long descent argument; it is isolated as one explicit auxiliary theorem so the target proof is a short formal composition.

## New nodes
`new-lem-sbc-etale-triples-prime-localization-component-extension-aux` records the auxiliary theorem.

## Earlier second reading (a previous round; superseded)
The target proof composes the auxiliary extension equation with naturality and cancellation; the target signature is unchanged. The auxiliary statement is a strict affine-model/factorization decomposition of the target.

## Second reading by K3

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and a proof-only import were added. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`. There are no errors, prohibited declarations, or hollow definitions. The target depends on `sorryAx` only through the explicitly split auxiliary theorem, as reported. Verdict: pass.
3. Checked the auxiliary statement and node. It is a strict decomposition supplying the model, extension, and factorization data needed by the target; its hypotheses and conclusion are unchanged and no duplicate library theorem was found. Verdict: pass.
4. The target proof uses the auxiliary theorem, category associativity, cocone naturality, and cancellation. The proof-only auxiliary import is minimal; no prior proof dependency is used directly. Verdict: pass.
5. The target and auxiliary nodes agree with the Lean declarations and the unit route remains the affine model/factorization route. Verdict: pass.

Changed only the target proof/import and added the auxiliary module and node; no statement or definition was changed.
