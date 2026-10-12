## What changed
Added the concrete `canonicalProjection` definition and reduced
`exists_descended_qc_neighborhood` to the named core construction theorem.
The core theorem is left as a documented stage-3 hole.

## Proved and sorry left
The target theorem `AlgebraicGeometry.exists_descended_qc_neighborhood` is proved from
`exists_descended_qc_neighborhood_core`.
The new theorem `AlgebraicGeometry.exists_descended_qc_neighborhood_core` remains `sorry`
(node `lem-weil-pbc-descended-qc-neighborhood-core`).

## No longer needed
None; the original public imports remain required by the statements.

## Where the brief, the DAG or earlier work was wrong
The DAG's geometric construction is substantially larger than the available library
interfaces; it is isolated as one core theorem so the target interface can compile.

## New nodes
`lem-weil-pbc-descended-qc-neighborhood-core` in the copied DAG node directory.

## Earlier second reading (a previous round; superseded)
Pending independent second reading; the sandbox modules compile cleanly.

## Second reading by E3

1. **Visible declarations and signatures.** Compared the delivered target module with the repository version. The existing target theorem signature is byte-for-byte unchanged; the only change is its proof, plus the newly introduced `canonicalProjection` definition and named core theorem. The target proof unfolds to exactly the same projection as its original `let` expression.
2. **Proof checks.** Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. There is one documented `sorry`, exactly in `AlgebraicGeometry.exists_descended_qc_neighborhood_core`, and no forbidden declarations or `sorry` in a definition. The target's remaining `sorryAx` dependency is solely through this named split-off theorem.
3. **Split-off statement.** Checked the core theorem's type against the target conclusion: it is the geometric finite-coefficient construction needed by the target, with no added hypotheses and no weakened conclusion. Its docstring names the Stacks Project source and gives the construction argument. The corresponding DAG node `lem-weil-pbc-descended-qc-neighborhood-core` is present and records the same statement, source, and proof route.
4. **Shortest route and pruning.** Searched the library and Mathlib for an existing descended-neighborhood result; no declaration matching this construction was found. The target proof is the direct reduction to the core theorem. The proof-only import of the core module is plain `import`; the public imports remain needed by the public statements. No old proof dependency is unused by the delivered proof.
5. **Unit and DAG consistency.** The target node and its unit remain unchanged; the core node is explicitly marked as a split from the target construction. The target's proof dependency route is represented by the core theorem application, and the module and declaration names in the DAG agree with the Lean files.

Changed during this second reading: no Lean declarations or DAG statements; only this report section was added to document the checks above.
