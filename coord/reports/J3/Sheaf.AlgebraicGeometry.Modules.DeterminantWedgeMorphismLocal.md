## What changed
Replaced both target sorries by applications of strictly smaller intermediate theorems. Added `DeterminantWedgeMorphismLocalAt` for the fixed-open construction and `DeterminantWedgeMorphismGlue` for gluing a chosen family.

## Proved and sorry left
The target declarations `determinant_wedgeMorphism_local_data` and `determinant_wedgeMorphism_of_local_data` are proved by real Lean applications. The two intermediate theorems `determinant_wedgeMorphism_local_data_at` and `determinant_wedgeMorphism_glue_family` remain sorry, each with its own node.

## No longer needed
None; all original imports remain needed by the intermediate statements.

## Where the brief, the DAG or earlier work was wrong
The DAG's two large proof obligations require substantial sheafification and gluing arguments; they were decomposed into fixed-open construction and chosen-family gluing interfaces.

## New nodes
`new-local-wedge-at` in `dag/nodes/sec-picard-framework/new-local-wedge-at.json` and `new-wedge-glue-family` in `dag/nodes/sec-picard-framework/new-wedge-glue-family.json`.

## Earlier second reading (a previous round; superseded)
The decomposition is mathematically faithful: the fixed-open theorem is strictly below the original universal statement, and the chosen-family gluing theorem is strictly below the existential-family statement. The target signatures are unchanged and the unit route is retained.

## Second reading by J3
1. Compared the delivered target module with the repository version. Both target signatures are byte-for-byte unchanged; only proof bodies and two proof-only imports differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry`s are the two named split theorems, with no forbidden declarations or hollow definitions. Verdict: pass.
3. Checked both split statements against their formal Lean declarations and the determinant paragraph. Each is a strict decomposition: one fixes an open, and the other takes a chosen family as input. Their DAG nodes and docstrings are present. Verdict: pass.
4. The proofs use the shortest available reductions in this module: universal local existence is obtained by applying the fixed-open theorem, and existential gluing by choice followed by the chosen-family gluing theorem. The unit route remains represented by the original target nodes. Verdict: pass.
5. Checked the DAG records, module imports, and mathlib/library search results. The records identify both new modules and declarations; no duplicate declaration exists; all imports are used by the declarations or split proofs. Verdict: pass.

Changed only the two target proof bodies, added their proof-only imports, and recorded this second reading. No statements, definitions, or DAG statement fields were changed.
