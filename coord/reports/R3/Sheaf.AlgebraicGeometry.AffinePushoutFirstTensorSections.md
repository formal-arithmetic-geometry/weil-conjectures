## What changed
The target theorem now combines two named intermediate presentations: the affine pushout ring section presentation and the affine first tensor module section presentation. Both are imported by proof-only imports and are explicit split points for the remaining algebraic geometry argument.

## Proved and sorry left
The target declaration `affine_pushout_first_tensor_sections` is proved by combining the two intermediate declarations. The intermediate declarations `affine_pushout_ring_section_presentation` and `affine_pushout_module_section_presentation` remain `sorry`, with nodes `lem-weil-pbc-affine-pushout-ring-section-presentation` and `lem-weil-pbc-affine-pushout-module-section-presentation`.

## No longer needed
No original proof dependency imports were removed. The target's direct proof uses the two new intermediate modules.

## Where the brief, the DAG or earlier work was wrong
The DAG plan expands a substantial sheafification and pushout calculation that cannot be closed in this worker interval; it is split into the ring and module section presentations, each strictly below the target and combined by a compiled proof.

## New nodes
`lem-weil-pbc-affine-pushout-ring-section-presentation` records the ring-section half. `lem-weil-pbc-affine-pushout-module-section-presentation` records the tensor-module half.

## Second reading by R3

1. I diffed the delivered target module against the repository version. The target
statement and all existing declaration signatures are unchanged; only proof imports
and the proof body were added.
2. I compiled all three delivered modules with `lcompile.py`. They compile without
errors and contain no forbidden declarations. The two split theorems are the only
remaining `sorry`s, and each is named in its node with a source and proof sketch.
3. The split statements are strict components of the target: the ring theorem gives
only the section map and additive generation, while the module theorem gives only the
linear equivalence and action/unit identities. Their signatures were copied verbatim
into the DAG `lean.statement` fields and their imports are proof-only where applicable.
4. The target proof follows the two split declarations directly. No old proof dependency
was removed, and no shorter proved declaration was available in the local library.
5. The unit route is retained: both split nodes belong to `sk-thm-p1`, and the target
continues to use the affine pullback comparison and tensor adjunction dependencies.

I repaired the split-node DAG records, added complete source/proof docstrings to the
ring and module split declarations, corrected the module blueprint identifier, and
recorded these checks here.
