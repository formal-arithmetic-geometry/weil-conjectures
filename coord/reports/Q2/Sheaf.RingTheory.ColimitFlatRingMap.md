## What changed

Proved `RingHom.eventually_flat_of_flat_stage` directly using `RingHom.Flat.lTensor`,
`Algebra.TensorProduct.cancelBaseChange`, and flatness under composition with ring
isomorphisms. All existing declaration signatures remain byte for byte unchanged.
Removed the proposed `Sheaf.RingTheory.FlatTensorBaseChange` module and its new node:
its holed theorem was just persistence with the final binders moved into hypotheses.
Removed seven unused private proof imports. Expanded the existing stage-existence
hole's docstring with its source and full natural-language proof.

Updated the persistence node to describe the completed Mathlib proof. Updated the
main node to describe its actual composition of the existing stage-existence and
persistence declarations. Preserved its original descent plan and dependencies on
the stage-existence node, where that unfinished argument belongs.

## Proved and sorry left

Closed one of the two original holes: `RingHom.eventually_flat_of_flat_stage`
(node `lem-weil-pbc-colimit-flat-ring-map-persistence`). Its axiom check shows only
`propext`, `Classical.choice`, and `Quot.sound`.

The sole remaining hole is the unchanged `RingHom.exists_flat_stage_of_colimit_flat`
(node `lem-weil-pbc-colimit-flat-ring-map-stage`). No new hole is added and no statement
is split off. The already-proved wrapper `RingHom.exists_eventually_flat_of_colimit_flat`
still depends on this hole, and its axiom check therefore includes `sorryAx`.
This delivery is a proof, not a decomposition: one hole closed, zero added.

## No longer needed

The following private imports are unused and removed:

- `Sheaf.Algebra.LimitFinitePresentation`
- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise`
- `Sheaf.RingTheory.ColimitCategoryFpAlgebras`
- `Sheaf.RingTheory.ColimitEventuallyFlat`
- `Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule`
- `Sheaf.RingTheory.OpenFlatLocus`

The proposed module `Sheaf.RingTheory.FlatTensorBaseChange` and node
`lem-weil-pbc-colimit-flat-ring-map-persistence-step` are deleted from the sandbox
before delivery; neither was part of the repository.

All old direct `proof_deps` of the main node are no longer directly used by its Lean
wrapper. They are retained on the stage-existence node's original descent plan,
so none of these DAG nodes is claimed to be globally dispensable:

- `lem-weil-pbc-directed-colimit-base-change-elementwise`
- `lem-weil-pbc-filtered-colimit-modules-criterion`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-finite-presentation-base-change-composition`
- `def-weil-pbc-finitely-presented-algebra`
- `lem-weil-pbc-limit-finite-presentation`
- `def-weil-pbc-noetherian-ring`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`
- `lem-weil-pbc-openness-of-flatness`
- `lem-weil-pbc-localization-tensor-over-base`
- `lem-weil-pbc-flat-module-base-change`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-localization-flat`
- `lem-weil-pbc-flat-ring-map-comp`
- `lem-weil-pbc-filtered-colimit-localization-at-prime`
- `lem-weil-pbc-colimit-eventually-flat`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-localization-tensor-product`
- `lem-weil-pbc-filtered-colimit-algebras-underlying-module`
- `lem-weil-pbc-flat-local-ring-maps`
- `lem-weil-pbc-flat-over-localization`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-filtered-colimit-rings-zero`
- `lem-weil-pbc-flat-map-local-criterion`
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
- `lem-weil-pbc-colimit-category-fp-algebras`
- `def-weil-pbc-flat-ring-map`

The main node now depends directly on the stage and persistence nodes. Global import
closure pruning is for the maintainer to measure; removal of an import here does not
assert that no other target imports the same module.

## Where the brief, the DAG or earlier work was wrong

The first worker's one-step assertion is logically equivalent to the persistence
assertion: introducing `i` and `hi` and applying it moves the entire argument into
another hole. Its docstring lacked a complete natural-language proof and the main
node had not been updated to match the claimed reduction. This second reading
replaces that restatement with an actual Mathlib proof and removes the new hole.
The remaining original existence docstring merely said to descend flatness; it is
now expanded. The Stacks source confirms its finite-presentation and colimit
hypotheses, and the local eventual-flatness criterion used in its plan is Tag 00R6.

## Second reading by Q2

1. Compared the complete module with the repository by `diff`, and compared parsed
   declaration signatures independently. Verdict: every existing signature is
   identical, with no definition or visibility change and no added hypothesis.
2. Compiled the delivered module locally through `lcompile.py`, and compiled a
   scratch copy with `#print axioms` for all three declarations. Verdict: persistence
   is kernel-checked with only the three allowed axioms; the other two declarations
   include `sorryAx` solely because of the reported stage-existence hole. No forbidden
   declarations, bypasses, hollow definitions, or arbitrary choices from open proofs.
3. Read the proposed split-off statement and checked the reflexive transitions,
   identity map, and trivial-ring cases. Its assertion is true but equivalent to the
   old hole, so the split is rejected and removed. Repeated searches with LeanFinder
   (flatness under extension of scalars), Loogle (`cancelBaseChange`), and grep in
   Mathlib and both project roots found the tools used for the direct proof.
   Verdict: no new statement or split-off hole remains.
4. Read from the wrapper downward and followed the shortest Mathlib route for
   persistence. Removed every unused private proof import and accounted for every
   old direct proof dependency above. Checked `dag/units/sk-thm-p1.json`: none of
   this item's nodes is a unit realization, and the unit statement and realized
   steps are untouched. Verdict: the descent route remains on the unfinished stage
   node; the completed persistence proof changes only a tool argument below it.
5. Compared all three node records with the declarations and proof bodies. Verdict:
   the main node records the two intermediate applications, persistence records
   Mathlib base change plus tensor cancellation, and stage-existence retains the
   original descent plan. No new node or change record is needed.

Changed during second reading: removed the equivalent split-off theorem and node,
wrote the direct persistence proof, pruned seven private imports, expanded the
remaining hole's source and proof docstring, synchronized three existing nodes,
and rewrote this report to distinguish a proved hole from the remaining one.
