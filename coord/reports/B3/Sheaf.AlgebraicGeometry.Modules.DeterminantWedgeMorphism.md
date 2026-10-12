## What changed
Added `DeterminantWedgeMorphismLocal.lean` with two named intermediate statements splitting local construction from gluing, and replaced the target proof by their composition. The target theorem now compiles with no sorry.

## Proved and sorry left
`determinant_wedgeMorphism_exists` is proved by applying the two intermediate statements. The new declarations `determinant_wedgeMorphism_local_data` and `determinant_wedgeMorphism_of_local_data` remain as named sorries; they are strictly the local construction and gluing steps.

## No longer needed
None; all original imports remain required by the target interface and intermediate statements.

## Where the brief, the DAG or earlier work was wrong
The planned proof contains two substantial independent arguments (local lift construction and sheaf gluing), so they were split into explicit intermediate nodes.

## New nodes
`lem-sc-determinant-wedge-morphism-local-data` and `lem-sc-determinant-wedge-morphism-glue`.

## Second reading by B3

1. Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and the new import differ. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; they compile cleanly. The target has no `sorry`; the two split statements retain named `sorry`s and have source, proof text, blueprint tags, and DAG nodes. Verdict: pass.
3. Checked the split statements against the target. They are true reductions: the local statement supplies per-open data and the gluing statement consumes that data to produce the global morphism. Their declarations are not present elsewhere in the library. Verdict: pass, with the caveat that the mathematical proofs remain open split nodes.
4. Checked the route and imports. The target still uses the local construction and gluing declarations; no original imports were removed, and the unit route remains represented by the target node. Verdict: pass.
5. Checked DAG agreement. Both new nodes now include verbatim Lean signatures, proof steps, proof dependencies, and three search records; their Lean declarations carry blueprint tags and proof docstrings. Verdict: pass.

Changed the two new theorem docstrings and completed both DAG node records with proof steps, dependencies, searches, and exact signatures. No target statement or definition was changed.
