## What changed

Added the arrow-level intermediate theorem
`AlgebraicGeometry.exists_selfTor_projection_homology_termwise_arrow`.  The target theorem now
constructs `asIso` from the supplied invertible arrow.  The intermediate theorem is the
projection-formula, K-flat representative, and exact-pushforward step that was missing from
the earlier attempt.

## Proved and sorry left

The target declaration `AlgebraicGeometry.nonempty_selfTor_projection_homology_termwise` is
proved from the arrow-level declaration.  The declaration
`AlgebraicGeometry.exists_selfTor_projection_homology_termwise_arrow` remains `sorry` and is
recorded by node `lem-pc-self-tor-projection-homology-termwise-arrow`.

## No longer needed

No imports were removed; all existing imports are retained for the stated projection-formula
route.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped after observing that no library theorem packages the representative
comparison.  Stage 3 permits this missing step to be stated as a named intermediate theorem;
the target can then be assembled by a real `asIso` construction.

## New nodes

`lem-pc-self-tor-projection-homology-termwise-arrow` records the arrow-level intermediate
statement and its source.

## Second reading by T4

1. **Interface unchanged.** Compared the delivered module with the repository version. The existing target declaration has the same signature byte for byte; the only added declaration is the explicitly recorded arrow-level split node.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no errors and the target proof contains no `sorry`. The remaining `sorry` is only `exists_selfTor_projection_homology_termwise_arrow`, named in the report and matched by its DAG node. The proof packages its supplied invertible arrow with `asIso` and introduces no forbidden declarations.
3. **Split statement.** Checked the arrow-level statement against the target: it is the strictly simpler existence of an invertible morphism whose `asIso` gives the target isomorphism, with the same hypotheses and displayed objects. Its source, proof description, searches, and Lean declaration are recorded in `lem-pc-self-tor-projection-homology-termwise-arrow.json`.
4. **Route and pruning.** The target follows the arrow-level projection-formula / representative-comparison route. No imports were removed, and no prior proof dependency is claimed unused; the unit route remains represented by the existing node and its new intermediate node.
5. **DAG agreement.** The target node's proof and `proof_deps` name the arrow-level theorem exactly as used in Lean. The new node records the exact theorem statement, declaration, source, proof origin, and dependency list.

Changed during second reading: used an ordinary local `let` for the proof-irrelevant `IsIso` witness, eliminating the proposition-style linter warning. No mathematical statement or import changed.
