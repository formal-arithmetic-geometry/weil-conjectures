## What changed

Proved `AlgebraicGeometry.RingedSpace.coherent_cokernel_relations` by reducing it to a local finite-free replacement theorem and the generic epimorphic-image finite-type theorem. Added the proof-only imports `CoherentCokernelRelationsLocal` and `FiniteTypeEpiImage`.

## Proved and sorry left

The target theorem `coherent_cokernel_relations` is proved. The new intermediate declarations `coherent_cokernel_relations_local` and `sheaf_finiteType_of_epi` remain as named `sorry`s, with nodes `lem-weil-pbc-coherent-cokernel-relations-local` and `lem-weil-pbc-sheaf-finite-type-epi`.

## No longer needed

None of the target's stated dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omitted the categorical restriction step needed to apply finite-type image preservation on the open restriction; this was split into the generic theorem `sheaf_finiteType_of_epi`.

## New nodes

`lem-weil-pbc-coherent-cokernel-relations-local` and
`lem-weil-pbc-sheaf-finite-type-epi-image` are added under `dag/nodes/sec-proper-base-change/`.

## Second reading by H2

1. Compared the delivered target module with the repository version. The theorem signature and
   its docstring are unchanged; only proof-only imports and the proof body were added.
2. Compiled all three sandbox modules with `lcompile.py --all`. There are no errors, axioms,
   unsafe declarations, or hollow definitions. The target is proved; the two named intermediate
   theorems remain the documented split-off `sorry`s.
3. Checked both split statements against the surrounding definitions and the Stacks 01BY route.
   The local replacement is the required finite-free/snake-lemma reduction. The epimorphic-image
   statement is the sheaf-ring generalization needed after restriction, and its node now records
   the complete local-generator proof rather than the unrelated local-replacement argument.
4. Searched the library and Mathlib. The existing `finiteType_image_extension` theorem covers
   ringed spaces, but no declaration covers arbitrary sheaves of rings on an open site; hence the
   proof-only generalization is needed and is not a duplicate declaration.
5. The unit route is retained: the target uses the local finite-free replacement, coherence of
   the resulting kernel, and epimorphic-image preservation. No unit-level statement or definition
   was changed.

Changed the split-node proof text and expanded the epimorphic-image theorem docstring. No imports
or DAG dependencies became unnecessary.
