## What changed
Added a core theorem `affineBaseChangeModelIsosCore` as a named decomposition carrying the remaining construction as a `Nonempty` proposition. The target theorem is proved by extracting its witness. The module otherwise keeps its original imports and statement.

## Proved and sorry left
The target theorem `AlgebraicGeometry.exists_affineBaseChangeModelIsosOfSchemeComparisons` is proved from the core decomposition. One sorry remains in `AlgebraicGeometry.affineBaseChangeModelIsosCore`, recorded in node `lem-pc-affine-base-change-model-isos-core`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The supplied plan requires a long categorical construction; no shorter closed proof was found within the session.

## New nodes
`lem-pc-affine-base-change-model-isos-core` records the named remaining construction.

## Earlier second reading (a previous round; superseded)
Pending independent second reading; the target compiles and the remaining core hole is named in the new node.

## Second reading by G4
1. I compared the delivered module with the repository version. The existing target
   declaration has the same signature byte for byte; only its proof and the documented
   core decomposition were added.
2. I compiled the module with `lcompile.py`; it compiles cleanly. There are no axioms,
   unsafe declarations, or hollow definitions. The only remaining `sorry` is the named
   theorem `AlgebraicGeometry.affineBaseChangeModelIsosCore`, with node
   `lem-pc-affine-base-change-model-isos-core`.
3. The split-off statement is true as the explicit `Nonempty` form of the construction,
   and the target obtains its witness by `.some`; its hypotheses and conclusion are
   unchanged and no additional assumptions are introduced.
4. The proof follows the supplied unit route and retains all original imports; no
   imports or proof dependencies were found to be removable.
5. The core node records the theorem statement, source, proof dependencies, and proof
   origin consistently with the Lean declaration. No existing declaration is duplicated.

I changed only the target proof, added the named core decomposition and node, and added
this second-reading record. No forced adaptations or statement changes were needed.
