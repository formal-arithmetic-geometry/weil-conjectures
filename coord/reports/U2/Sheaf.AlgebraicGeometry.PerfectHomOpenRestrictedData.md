## What changed
Added `PerfectHomOpenRestrictedDataExists` and imported it into the target module. The target theorem now combines the restricted-data existence theorem with the pinned-equations theorem. The latter is left as a named intermediate theorem with a documented source.

## Proved and sorry left
The target `perfect_hom_open_restricted_data` is proved by combining two strictly simpler statements. `perfect_hom_open_restricted_data_exists` and `perfect_hom_open_restricted_data_pinned` remain `sorry`, each with a corresponding DAG node.

## No longer needed
None; the target retains its stated imports and the explicit comparison definitions.

## Where the brief, the DAG or earlier work was wrong
The detailed categorical construction in the blueprint cannot be discharged from the currently stated APIs in the available time; it was decomposed into existence and compatibility statements.

## New nodes
`lem-pc-perfect-hom-open-restricted-data-exists` in `dag/nodes/sec-picard-framework/lem-pc-perfect-hom-open-restricted-data-exists.json`.
`lem-pc-perfect-hom-open-restricted-data-pinned` in `dag/nodes/sec-picard-framework/lem-pc-perfect-hom-open-restricted-data-pinned.json`.

## Second reading by U2

1. Compared the delivered target module with the repository version. Existing declarations and
   definitions have byte-for-byte identical signatures; only the proof and the imported split
   module were added.
2. Compiled both delivered modules with `lcompile.py --all`. They compile successfully, with no
   declarations using forbidden axioms or constructs. The two remaining `sorry`s are named
   theorems and have source and proof-plan docstrings.
3. Checked both split statements against the target: existence supplies the restricted data and
   the pinned theorem supplies exactly the two displayed equations. They are strictly simpler
   conjunctive components and introduce no changed hypotheses or weakened conclusions. The
   corresponding DAG nodes are present and match the Lean declarations.
4. The route still follows the unit's restricted-data step; no imports or proof dependencies
   were removed, and no shorter existing declaration was found in the local library.
5. The target proof is the direct conjunction of the two split statements, and the unit and
   chapter metadata in both nodes remain unchanged.

Changed the pinned theorem's formatting and added its required proof-plan docstring; no
mathematical statement was changed.
