## What changed

Proved `AlgebraicGeometry.affine_chart_section_ring_presentations_iso` without any
new declarations or hypotheses. The proof extracts both preorder inequalities
from equality of antisymmetrization classes, constructs the inverse preorder
arrow, transports invertibility through R and Spec, and uses Mathlib's
`pullback_snd_iso_of_left_iso` instance. The statement and its visibility are unchanged.
Updated the item's DAG proof to describe these three elementary steps.
The public-import pruning is recorded in
`coord/changes/affine-chart-section-ring-presentations-iso-imports.md`.
The sole direct importer already imports all removed modules independently;
no adaptation is needed.
Replaced the three unnecessary public imports listed below with the direct
statement dependencies `Mathlib.AlgebraicGeometry.Pullbacks` and
`Mathlib.CategoryTheory.Category.Preorder`; retained
`Mathlib.Order.Antisymmetrization`.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.affine_chart_section_ring_presentations_iso`
(node `new-affine-chart-section-ring-presentations-iso`).
No sorry remains in the delivered module. No holes or modules were added.
The proof uses only Mathlib, with no unproved project theorem.
The final dry run checks the declaration's axioms.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
  (node `def-pc-base-change`): none of its base-change definitions or theorems is used.
- `Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitData`
  (node `new-affine-chart-upper-tail-limit-data`): no limiting-cone theorem is used.
- `Mathlib.Algebra.Category.Ring.Colimits`: no ring-colimit construction is used.

These modules and nodes are unnecessary for this item's proof. This does not
assert that they are absent from other targets' import paths.
The item's existing proof_deps was empty and remains empty; the proof now
explicitly identifies its Mathlib arguments. The unit's realized lists are empty,
so this removes no realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The existing declaration docstring claims that the chosen representative is
literally `(j, le_rfl)` and that its transition map is an identity. That claim
need not hold for a preorder: quotient representatives are only related in
both directions to the original index. The statement is nevertheless true,
and the proof uses this weaker, correct representative law. The original
DAG's single step gave no actual argument; its replacement records the proof.
The proof covers non-antisymmetric preorders and arbitrary rings and schemes;
there is no use of directedness beyond the unchanged theorem signature.

## Second reading by U2

1. **Signatures and visibility — PASS.** I compared the delivered declaration
   byte-for-byte with the repository version. Its theorem signature,
   hypotheses, conclusion, namespace, and public visibility are unchanged.

2. **Proof and axioms — PASS.** The module compiles with
   `lcompile.py`; the theorem has no `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`. The proof uses only quotient
   antisymmetrization, preorder hom-set subsingletons, functoriality, and the
   Mathlib pullback isomorphism instance.

3. **Statements and dependencies — PASS.** No new Lean statement was added.
   The existing theorem is true for arbitrary preorders (the representative
   need only be equivalent to `(j, le_rfl)`), and the proof does not add a
   hypothesis or weaken the conclusion. The DAG proof steps now match the
   Lean proof, and the import change is recorded in the change record.

4. **Pruning — PASS.** The removed project and ring-colimit imports are not
   referenced by the proof. The replacement Mathlib imports are minimal for
   the public statement and proof. No realized unit statement or step is
   removed.

5. **Route and nodes — PASS.** The unit `sk-thm-picard-semicon` has no
   realized entries for this node, so its route is unchanged. The existing
   node records the theorem statement verbatim and the three elementary proof
   steps; no additional split-off hole or node is introduced.

I changed only the theorem proof and its DAG proof metadata, pruned the
   imports with the accompanying change record, and added this second-reading
   report section.
