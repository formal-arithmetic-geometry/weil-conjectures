## What changed
Split the target theorem into three named component declarations in the same module: target-comparison invertibility and the two independent normalization equalities. The target theorem is proved by combining these components.

## Proved and sorry left
The target theorem `schemeTensorShift_localization_normalization` is proved. The component declarations `schemeTensorShift_targetComparison_isIso`, `schemeTensorShift_first_normalization`, and `schemeTensorShift_second_normalization` remain sorry and have DAG nodes `aux-sc-target-comparison-isIso`, `aux-sc-target-comparison-first`, and `aux-sc-target-comparison-second`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned calculation has no existing Lean theorem closing the three independent components; they are split as explicit obligations.

## New nodes
Added nodes `aux-sc-target-comparison-isIso`, `aux-sc-target-comparison-first`, and `aux-sc-target-comparison-second`.

## Earlier second reading (a previous round; superseded)
Pending second worker review.

## Second reading by E4
1. Compared the delivered module with the repository version. Existing declarations,
definitions, and target signatures are unchanged; only the parent proof and its three
named component declarations were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The only remaining
`sorry`s are the three explicitly named component theorems, and no forbidden declaration
or hollow definition was introduced.
3. Checked the component statements against the parent conjunction. Each is a strict
substatement needed by the parent proof. Their documentation gives the Stacks Project
source and the complete calculation used to justify each split. The DAG nodes are present,
and their proof dependencies now point to the parent theorem's mathematical dependencies,
not back to the target node.
4. The shortest available route was checked by searching the Sheaf and WeilConjectures
trees for existing comparison or normalization lemmas; none closes these calculations.
The three imports are all used by the public statements or their required instances, so
no import can be pruned.
5. The unit route is preserved: the target comparison, first normalization, and second
normalization are exactly the three steps of the recorded localization normalization unit.

Changed the three component docstrings to include proof sketches and sources, and repaired
the three node proof records and dependencies. No definitions or public signatures changed.
