## What changed

The target theorem now combines two named intermediate results: existence of a coefficient
function satisfying the numerator equation, and the arithmetic laws forced by that equation.
Both intermediate declarations are in separate modules and are imported privately by the target.

## Proved and sorry left

The target hole `exists_sectionRing_coefficient_data` is closed by combining the two
intermediate declarations.
The intermediate declarations `exists_sectionRing_coefficient_numerator` and
`sectionRing_coefficient_arithmetic_of_numerator` remain `sorry`, with nodes
`lem-sc-section-ring-coefficient-data-numerator` and
`lem-sc-section-ring-coefficient-data-arithmetic`.

This is a decomposition, not a completed axiom-free proof: one original hole closed,
two holes added, net minus one. No arbitrary object is defined from an unproved
existence statement.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The planned construction consists of two independently substantial parts; the original module
had no declarations exposing these parts, so they were split into named nodes.

## New nodes

`lem-sc-section-ring-coefficient-data-numerator` and
`lem-sc-section-ring-coefficient-data-arithmetic` are new decomposition nodes.

## Second reading by D4

1. Compared each delivered module with the repository version. The target theorem signature is
   unchanged; only proof imports and the proof body were added, and the two new modules contain
   the statements recorded by their nodes.
2. Compiled all three modules with `lcompile.py`. They compile successfully and contain no
   forbidden declarations; the only remaining `sorry`s are the two named split-off theorems.
   Scratch `#print axioms` checks of all three theorems show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`.
3. Checked the split-off statements against the target and searched the library and Mathlib for
   duplicates. Each is a strict decomposition (numerator existence and arithmetic consequences)
   and neither is an existing declaration. Checked n=0, zero numerators, the empty open,
   and torsion/zero-divisor cases: cancellation uses the local free generator, never s
   in the global ring. Expanded both docstrings into complete natural-language proofs.
4. The target proof uses both private imports, while the public imports are required by the
   signatures. No unused import or old proof dependency was identified.
5. The node records match the Lean declarations and retain unit `sk-thm-curveestimate`; the
   target route is preserved through the coefficient-data node. Updated its proof and
   dependencies to cite the two actual intermediate nodes. The unit's realized statement
   is thm-sc-proper-cohomology and has no realized proof steps; neither is bypassed.

Changed during this reading: expanded the incomplete docstring proofs, removed proof bodies
from the new nodes' lean.statement fields, repaired the target node's proof route, removed
inherited review metadata from the new nodes, and recorded the decomposition and axiom checks.
No Lean signature or proof body required repair.

## Earlier second reading (a previous round; superseded)

Pending second reading by the group.
