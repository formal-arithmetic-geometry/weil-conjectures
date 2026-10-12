## What changed
Reviewed the target module. Removed the invalid helper decomposition: its map-properties statement discarded the naturality hypotheses by replacing them with `True`, so it could not support the target. Proved `CategoryTheory.tower_limit_projection_surjective` directly using Mathlib's surjective projection theorem, restricting along the cofinal shift `n ↦ m+n`; the target theorem remains open.

## Proved and sorry left
Closed `CategoryTheory.tower_limit_projection_surjective`. `CategoryTheory.tower_limit_exact_surjective_kernels` remains `sorry`.

## No longer needed
Removed the split-off helper declarations and their two new nodes. No project proof-dependency imports were needed; the proof uses plain imports of `Mathlib.CategoryTheory.Filtered.Final` and `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`.

## Where the brief, the DAG or earlier work was wrong
The earlier worker's `tower_limit_map_properties` declaration weakened both naturality assumptions to `True`, making its statement insufficient for the documented coordinatewise proof. The cofinal-shift argument closes part (a) via an existing Mathlib theorem and avoids that invalid split.

## Second reading by E1
1. Compared the delivered module with the repository version. Existing target signatures are unchanged; only the projection proof and proof imports changed, and the invalid helper declarations were removed.
2. Compiled the module with `python3 /home/ubuntu/weil-launcher/lcompile.py`; it compiles. The only remaining `sorry` is the named target theorem. No definitions contain `sorry`, and no forbidden declarations occur.
3. Checked the projection statement on arbitrary `m`; the proof uses the cofinal shift and Mathlib's `surjective_π_app_zero_of_surjective_map`, with no weakened hypotheses. The target remains exactly the repository statement.
4. Pruned the unsound helper decomposition and updated the DAG proof/proof-dependency route to the Mathlib declarations actually used.
5. The unit route is preserved: this proves only the projection substep (a), while the inverse-limit exactness target remains open.

## New nodes
None.
