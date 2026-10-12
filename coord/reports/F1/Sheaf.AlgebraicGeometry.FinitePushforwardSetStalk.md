## What changed
Split the target into two named intermediate theorems: finiteness of the geometric fibre and bijectivity of the restriction map assuming that finiteness. The target theorem is proved by combining these two statements. Added the corresponding imports.

## Proved and sorry left
`AlgebraicGeometry.finite_pushforward_set_stalk_bijective` is proved by a real conjunction of the two intermediate results. The intermediate declarations `finite_pushforward_set_stalk_fiber_finite` and `finite_pushforward_set_stalk_map_bijective_of_finite` remain `sorry`, with nodes `lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite` and `lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective`.

## No longer needed
None; the original proof dependencies remain available for the intermediate map theorem.

## Where the brief, the DAG or earlier work was wrong
The ten-step geometric proof is too large to complete in this item window, so its two substantive stages were split into independently provable statements.

## New nodes
Added `lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite` and `lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective`.

## Earlier second reading (a previous round; superseded)
The target signature is unchanged. The two new statements are strict components of the conjunction and preserve the intended route: one worker can prove fibre finiteness and another the restriction bijection.

## Second reading by F1
1. I compared the delivered target module with the repository version. The theorem
   signature and all existing declarations are unchanged byte for byte; only proof
   text and the imports needed by the split lemmas were added.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors. The only remaining `sorry`s are the two named split theorems,
   each with a matching DAG node; there are no definitions containing `sorry` and
   no prohibited declarations.
3. The split statements are strict components of the target conjunction: one gives
   fibre finiteness and the other gives bijectivity conditional on that finiteness.
   Their docstrings now record the Stacks source and the complete geometric proof
   outline. No duplicate declaration was found in the library.
4. The target proof uses both split declarations directly. All imports required by
   their signatures and proof route remain present; no unused import can be removed
   without hiding a declaration used by the route. The DAG records the two new
   declarations and their split status.
5. The ten-step unit route is preserved in the target docstring and in the split
   nodes' source and proof records. No target statement or definition was changed.

I repaired the report by adding this second-reading section and expanded both split
theorem docstrings with their source and proof outlines. No mathematical statement
or proof term was changed.
