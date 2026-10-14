## What changed

Added a proof reduction for `standardSingleFlatCounit_localization_completion`. The target now obtains the bounded flat stalk complex from `standardSingleFlatCounit_localization_data`, obtains the derived scalar-extension pair from `standardSingleFlatCounit_localization_pair`, and combines these with the fixed-data homology theorem. Added the two intermediate theorem modules and their DAG nodes.

## Proved and sorry left

The target theorem is proved by composition. `standardSingleFlatCounit_localization_pair` remains a named sorry, and `standardSingleFlatCounit_localization_homology` remains a named sorry; both are strictly lower statements with DAG nodes.

## No longer needed

No imports or planned dependencies were removed. The direct presentation import remains required by the target statement.

## Where the brief, the DAG or earlier work was wrong

The checked-out module had acquired localized presentation parameters `(S, V, hS, hV, hSaff, hVaff, hVS, hpres)` while its earlier DAG description still described only the affine hypothesis. The proof follows the checked-out signature and preserves it unchanged.

## New nodes

`lem-pc-standard-single-flat-counit-localization-pair` records existence of the derived scalar-extension pair. `lem-pc-standard-single-flat-counit-localization-homology` records the remaining degreewise homology identifications and compatibility for fixed data.

## Earlier second reading (a previous round; superseded)

The decomposition statements are strictly below the target: one supplies only the derived pair, and the other supplies homology data for a fixed pair. The target signature is unchanged.

## Second reading by B2

1. **Unchanged statements.** Compared the delivered completion module byte-for-byte with the repository version. The theorem signature is unchanged; the two newly added theorem signatures are recorded by their nodes and are used only as proof reductions.

2. **Compilation and proof hygiene.** Compiled all three sandbox modules with `lcompile.py --all`; they compile cleanly. The completion proof contains no `sorry`; the only remaining `sorry`s are the named split-off theorems `standardSingleFlatCounit_localization_pair` and `standardSingleFlatCounit_localization_homology`. No forbidden declarations or hollow definitions occur. The completion theorem's axioms contain only the permitted foundational axioms plus `sorryAx` inherited from those two open lower theorems.

3. **Statements and nodes.** Checked the split-off declarations against their node statements and searched the local library for duplicates. Both are strictly smaller than the completion target: the pair theorem supplies only the derived scalar-extension pair, while the homology theorem handles the fixed data and degreewise compatibility. Their DAG nodes and the completion node now match the proof calls and dependencies.

4. **Pruning.** The proof uses localization data, the derived pair, and fixed-data homology. The previous direct presentation and stalk-comparison dependencies are therefore no longer direct proof dependencies; the target's node has been updated accordingly. The public presentation import remains required by the target signature, while proof-only imports remain private.

5. **Unit route.** The proof follows the localization route by first constructing P from localization data, then obtaining the derived pair, and finally transporting homology and counit compatibility. No unit statement or definition was changed.

Changed the target DAG proof and dependency records to reflect the actual composition, and added this second-reading record. No Lean statement or definition was changed.
