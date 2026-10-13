## What changed

Filled `completedRingMap_torsion_kernel_zero` without changing its signature, visibility,
existing docstring or any definition. Retained and used the first worker's proved private
`pushout_torsion_descends` helper. Proved `punctured_torsion_section_zero` as a private
helper with Mathlib's stalk separatedness and basic-open API. The target descends torsion
through the completion, kills both matching coordinates, and uses concrete pullback
extensionality. All four added imports are proof-only imports.

## Proved and sorry left

Closed the repository hole
`AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_torsion_kernel_zero`
(1 of 1). Closed the first worker's punctured-section hole in
`punctured_torsion_section_zero`. Removed the proposed
`matchingRing_torsion_completed_zero`, which merely restated the target. Both
private helpers are proved. Added no holes, split off no statements, and left no
local sorry. The target's `#print axioms` gives exactly `propext`, `Classical.choice`
and `Quot.sound`; no `sorryAx` is reachable. This is a proof, not a decomposition.

## No longer needed

No repository import or module is pruned. Removed the first worker's unused
`Mathlib.AlgebraicGeometry.StructureSheaf` proof import, both proposed split-off
nodes (including duplicate misplaced files), and the unnecessary proof-import change
record. Ordinary private proof imports require no interface-change record.
The old proof dependency `def-weil-finite-integral-morphism` is no longer used by
the argument, and was removed from `proof_deps`; it remains in `stmt_deps` because
the unchanged target still assumes finite q and s. Every other old proof dependency
is retained. The unit's realized fields are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original report claimed that a renamed copy of the target was a strictly smaller
step. It was a restatement and its punctured-section hole was unused. The geometric
vanishing can be proved directly with `germ_eq_zero_of_pow_mul_eq_zero` and
`TopCat.Presheaf.section_ext`, without a finite affine-cover construction.
The proposed new node records lacked self-contained statements and concrete proof
steps. They are removed, rather than delivered. No definition or statement correction
was needed.

## Second reading by N3

1. Compared the complete module diff with the repository version and checked the
   existing theorem signature byte for byte through its `:=`. All hypotheses,
   quantifiers, conclusion and visibility agree; the public import and definitions
   are unchanged. Only private helpers, proof imports and the proof are added.
2. Compiled the delivered module and a scratch copy with `#print axioms`. No compiler
   errors or warnings, no local sorry and no forbidden declarations. The target uses
   only the three allowed axioms, including through the torsion base-change theorem.
3. No split-off statement remains. Independently searched with LeanFinder for sections
   over a punctured local spectrum annihilated by the maximal ideal and with Loogle for
   completion residue-field bijectivity. LeanFinder found
   `germ_eq_zero_of_pow_mul_eq_zero`, which is used in the completed proof. Local `rg`
   searches checked scheme basic opens, stalk extensionality, completion flatness,
   quotient maps and concrete limit extensionality. The generic descent lemma allows
   a different exponent k; the geometric helper covers arbitrary Y over U. At n=0,
   1 annihilates the section. If U or Y is empty, section extensionality has no points
   to check; zero component rings require no nontriviality assumption.
4. Read [05EC](https://stacks.math.columbia.edu/tag/05EC),
   [05ER](https://stacks.math.columbia.edu/tag/05ER),
   [05EU](https://stacks.math.columbia.edu/tag/05EU) and
   [0BLH](https://stacks.math.columbia.edu/tag/0BLH). The proof follows the original
   torsion descent and jointly injective matching-coordinate route. The stalk proof
   supplies the localization step directly. Checked the unit
   `sk-prop-input-spreading`: this node realizes no unit statement or step; no unit
   route is bypassed. Added imports provide respectively the torsion theorem, tensor
   pushout comparison, completion flatness and completion residue-field facts; the
   unused StructureSheaf import was removed. The No longer needed section lists the
   entire old proof-dependency difference.
5. Rewrote the existing node's proof steps, their union `proof_deps` and `proof_origin`
   to match the completed Lean argument. Its statement, statement dependencies, source,
   Lean signature, chapter and unit are unchanged. No new node is needed for a hole.

Changes made in this reading: replaced the target restatement with the actual torsion
reduction, proved punctured-section vanishing, removed all new holes and proposed nodes,
removed the unused import and unnecessary change record, and corrected the DAG and report.

Preflight repair: replaced global tensor-product scoped notation with explicit
`TensorProduct` and `TensorProduct.tmul` names, so no visible command is added.
