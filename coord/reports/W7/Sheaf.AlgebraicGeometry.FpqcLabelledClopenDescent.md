## What changed

Replaced the proof of
`AlgebraicGeometry.labelledClopenPartition_existsUnique_of_fpqc` in
`Sheaf.AlgebraicGeometry.FpqcLabelledClopenDescent` with the four-step argument
already specified by `lem-sfb-fpqc-labelled-clopen-descent`.

For each label, apply the existing `openSubscheme_existsUnique_of_fpqc` to its
compatible open fibres. Joint surjectivity identifies membership with the label
of any lift. This proves pairwise disjointness, exhaustiveness, and uniqueness.
The complement of each piece is the union of pieces indexed by other labels,
which proves closedness without any finiteness hypothesis. For a test morphism,
`Precoverage.mem_coverings_of_isPullback` gives an fpqc covering by second
projections. Lifting a test point to this covering and evaluating the pullback
equation and the label compatibility proves the preimage equality. Continuity
gives clopenness.

The theorem signature, docstring, imports, definitions, and DAG route are
unchanged. The proof handles empty label types and empty covering index types
without adding nonemptiness assumptions. No arbitrary data is defined from an
existence theorem: the descended opens are the uniquely determined opens of the
existing descent theorem, used locally within a proof.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.labelledClopenPartition_existsUnique_of_fpqc`
(node `lem-sfb-fpqc-labelled-clopen-descent`). One of one original holes closed;
zero holes added, zero split off, and zero holes remain in the delivered module.

## No longer needed

None. No imports removed, no modules withdrawn, and no planned dependencies
pruned. The proof uses the existing fpqc open-subscheme descent theorem and the
Mathlib fpqc base-change result named in the node. The unit's fpqc descent route
is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancies found. Read Stacks `descent.tex`,
`lemma-open-fpqc-covering` (Tag 03N0), and `topologies.tex`, `lemma-fpqc` part (3)
(Tag 022D), as well as the lattice unit and all six cited dependency statements.
Searches of LeanFinder, Loogle, Mathlib, and the existing two source roots found
no theorem that directly proves the complete labelled partition and test clause.
The existing open-subscheme descent theorem supplies exactly the needed input.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
