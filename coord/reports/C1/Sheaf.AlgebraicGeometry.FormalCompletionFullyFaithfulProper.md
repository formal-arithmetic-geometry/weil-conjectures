## What changed
The target bijectivity theorem is proved by combining separate injectivity and surjectivity statements. Two auxiliary modules state those strictly simpler parts and are imported by the target module.

## Proved and sorry left
The target `formalCompletion_map_bijective_of_proper` is proved. Sorry remains in `formalCompletion_map_injective_of_proper` and `formalCompletion_map_surjective_of_proper`, each split into a strictly simpler property.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned categorical composite proof was not executable within the available interfaces; the argument was decomposed into injectivity and surjectivity obligations.

## New nodes
`lem-weil-pbc-formal-completion-map-injective-proper` and `lem-weil-pbc-formal-completion-map-surjective-proper`.

## Earlier second reading (a previous round; superseded)
Pending second reading.

## Second reading by C1

1. I compared the target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports of the two auxiliary modules and the proof body were added. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without errors or warnings. The target has no `sorry`; the only remaining holes are the two explicitly named split theorems, with no hollow definitions or forbidden declarations. Verdict: pass.
3. The two split statements are true strict consequences of bijectivity and are needed to compose the target proof. I checked their exact signatures against the target map and found no existing duplicate declaration in the library. Their node statements and proof plans now spell out the full map and the internal-Hom/formal-functions reduction. Verdict: pass.
4. The proof uses the shortest available route: `Function.Bijective` is constructed directly from the injective and surjective components. No additional imports were removable from the target or auxiliary modules, and the unit route remains represented by the target node. Verdict: pass.
5. The DAG nodes now match the Lean declarations, including complete statements, proof dependencies, origins, and split status. Verdict: pass.

Changed the two auxiliary theorem docstrings to include complete proof descriptions, and repaired both split-node metadata records with self-contained statements and the dependencies used by their proof plans.
