## What changed
Added two intermediate theorem modules splitting the target into local-to-global and global-to-local directions. The target proof combines them; global-to-local is proved using functorial preservation of isomorphisms.

## Proved and sorry left
`projectionFormula_isIso_iff_openCover` is proved from the two directional theorems. `projectionFormula_global_to_local` is proved. `projectionFormula_local_to_global` remains `sorry` in node `lem-pc-projection-locality-local-to-global`.

## No longer needed
None beyond the existing imports; all stated dependencies remain available for the unsolved local-to-global direction.

## Where the brief, the DAG or earlier work was wrong
The original theorem requires a substantial derived-category locality argument not represented by an existing Lean declaration; it was split into directional intermediate statements.

## New nodes
`lem-pc-projection-locality-local-to-global` and `lem-pc-projection-locality-global-to-local`.

## Earlier second reading (a previous round; superseded)
The target statement is unchanged. The global-to-local intermediate is proved by `Functor.map_isIso`; the local-to-global intermediate is exactly the remaining derived locality argument and is left as a named node. The unit route is retained.

## Second reading by C1

1. Compared the delivered target module with the repository version. The target
   declaration and all existing signatures are unchanged; only proof imports and
   the proof body were added.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile
   without errors. The only remaining `sorry` is the named theorem
   `projectionFormula_local_to_global`, recorded by node
   `lem-pc-projection-locality-local-to-global`; no definitions contain `sorry`.
3. The global-to-local theorem is exactly the functorial preservation of
   isomorphisms. The local-to-global theorem states the converse direction of
   the target and retains the derived-category locality argument as a named
   split node, with its source and proof obligation documented.
4. The proof uses the existing derived-category and restriction imports; no
   unused import was identified. The DAG child nodes match the Lean theorem
   names and signatures, and the unit route remains represented by the target
   node and its two directional steps.
5. No target statement or existing declaration was changed, and no additional
   axiom, unsafe declaration, or hollow definition was introduced.

Changed only this report after the review; no code repair was needed.
