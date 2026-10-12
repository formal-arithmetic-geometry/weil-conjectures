## What changed
Split the degree-zero dictionary into three named intermediate statements and proved the target by combining their witnesses. The intermediate proofs remain explicit stage-3 holes.

## Proved and sorry left
The target `formalFunctions_degreeZero_dictionary` is proved by a real Lean construction from `formalFunctions_degreeZero_stalkIso`, `formalFunctions_degreeZero_systemIso`, and `formalFunctions_degreeZero_compatibility`. The three intermediate declarations retain `sorry` proofs, with nodes matching each declaration.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned construction requires substantial derived-category and restriction coherence not available as proved declarations, so it was decomposed into the three strict component statements.

## New nodes
`lem-weil-pbc-formal-functions-degree-zero-stalk-iso`, `lem-weil-pbc-formal-functions-degree-zero-system-iso`, and `lem-weil-pbc-formal-functions-degree-zero-compatibility`.

## Second reading by C2

1. **Interface comparison.** Compared the delivered dictionary module with the repository version. The target declaration and all existing declaration signatures are unchanged; only the proof and its necessary imports were added.
2. **Proof and axioms.** Compiled all four delivered modules with `lcompile.py`; there are no errors, unsafe declarations, or hollow definitions. The target is proved by applying the three named component declarations. The component theorems are the only remaining named `sorry` declarations.
3. **Split statements.** Checked the three component statements against the target: the stalk and system statements provide only their respective witnesses, while compatibility takes those witnesses as arguments and proves only the compatibility formula. Their node metadata now depends on the underlying definitions and component lemmas rather than circularly on the target.
4. **Pruning and imports.** The original public interface import remains necessary for the target statement. Proof-only imports remain plain imports; no unused import was identified after compilation. The unit route is preserved because the dictionary still factors through the stated degree-zero stalk, system, and compatibility steps.
5. **DAG agreement.** Updated each split node's `stmt_deps` and `proof_deps` to remove the target self-dependency and match the declarations used by the module. No target statement or definition was changed.

Changed in this second reading: repaired the three split-node dependency records, fixed the overlong compatibility declaration line, and added this review record.
