## What changed
Proved `exists_tensorMap` by applying the tensor-product algebra lift to an intermediate compatible-stalk-algebra-map theorem. Added the named intermediate theorem `exists_stalk_algebra_maps`, whose proof remains a documented sorry. No imports were added or removed.

## Proved and sorry left
The proof of `exists_tensorMap` is closed. The following declarations remain sorry: `exists_stalk_algebra_maps` (node `lem-single-complex-stalk-algebra-maps`), `exists_tensorStalkIso`, and `nonempty_coordinates` (both recorded by the item node `def-pc-single-complex-base-change-stalk-condition`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original node omitted the concrete intermediate compatibility theorem needed to construct the tensor-to-stalk map; it is added as a strictly simpler new node.

## New nodes
`lem-single-complex-stalk-algebra-maps` is the intermediate theorem stated in this module.

## Second reading by T4

1. Compared the sandbox module with the repository version. Existing declaration signatures and
   definitions are unchanged; the only added declaration is the documented intermediate theorem,
   and `exists_tensorMap` has only a proof change.
2. Compiled the module with `lcompile.py`; it is clean apart from style warnings. The only remaining
   sorries are the three named in the preceding section, and no forbidden declarations or hollow
   definitions were introduced.
3. Checked the new statement against the tensor-product construction and searched the library for
   existing stalk-map compatibility results. It is a strictly smaller compatibility statement,
   with its source and node recorded above; no duplicate declaration was found.
4. The proof uses the new intermediate theorem and `Algebra.TensorProduct.lift`; all original
   imports remain needed, and no proof dependency is pruned.
5. The unit and chapter route are unchanged: the original item remains the carrier of the
   tensor-to-stalk and coordinate definitions, while the added node supplies only the missing
   compatibility step.

Changed after review: verified the proof by compilation and documented the second reading; no
Lean repair was necessary.
