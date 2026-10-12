## What changed

Proved `Algebra.exists_smoothAtPrime_conormal_data` from the split conormal localization
lemma and a new selected-basis localization theorem. Added the new module
`Sheaf.RingTheory.SelectedBasisOfLocalizedSplit`; its theorem remains a named intermediate
`sorry` because the final transport through iterated localizations was not completed.

## Proved and sorry left

Closed `Algebra.exists_smoothAtPrime_conormal_data`. The new theorem
`Module.exists_selected_basis_away_mul_of_split` remains `sorry`, with node
`lem-weil-pbc-selected-basis-of-localized-split`.

## No longer needed

The original parent proof dependency `lem-weil-pbc-smooth-at-prime-free-conormal-basis` is
not needed by this proof. No imports were removed from the item module.

## Where the brief, the DAG or earlier work was wrong

The item's original DAG proof dependency pointed to its parent theorem, creating a circular
route. The proof dependencies now follow the split conormal sequence and the selected-basis
intermediate theorem.

## New nodes

`lem-weil-pbc-selected-basis-of-localized-split` records the strictly smaller basis-selection
and localization-spreading statement in `Sheaf.RingTheory.SelectedBasisOfLocalizedSplit`.

## Earlier second reading (a previous round; superseded)

The item module compiles. The new intermediate theorem is strictly smaller than the item and its statement matches the Lean declaration; the unit route through the split conormal sequence is retained.

## Second reading by S3

1. **Declarations unchanged.** I diffed the item module against the repository version. The
existing theorem signature is unchanged byte for byte; only proof imports and proof terms were
added. The selected-basis theorem is a new, strictly smaller declaration recorded by its node.

2. **Proof and axioms.** Both delivered modules compile with `lcompile.py`. The item theorem has
no `sorry`; the only remaining `sorry` is the explicitly named selected-basis intermediate, which
has a node and a complete proof plan. No forbidden declarations or hollow definitions were added.

3. **Statements and prior work.** I searched the repository and ran leanfinder for the selected
basis result. No existing declaration duplicates it. Its hypotheses and conclusion are the exact
finite-generation, split-localization, principal-neighborhood statement needed by the item, and
the edge case of an empty generating family is covered by the quantified formulation.

4. **Pruning and imports.** The item uses the split conormal theorem and the selected-basis
intermediate; its original circular parent dependency is removed from the node. The selected-basis
proof itself uses only its Mathlib imports, so its node has no library proof dependencies.

5. **DAG and route.** The item node's proof, proof dependencies, and origin now match the Lean
proof. The unit route through the split conormal sequence is retained. The selected-basis node
records the decomposition and its Lean declaration exactly.

I changed the DAG dependency metadata for the selected-basis node and added this second-reading
record; no Lean statements or definitions were changed.
