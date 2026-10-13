## What changed

Preserved the existing target signature byte for byte and replaced its `sorry` with a proof
that obtains a natural fibre dimension, obtains chart data for that dimension, and assembles
the witnesses. Added two proof-only imports and two modules. During second reading, proved
`AlgebraicGeometry.exists_fiber_dimension_nat` using the upstream finite-type dimension bound.
Suppressed the existing unused `hy` binder warning locally, without renaming the binder.

## Proved and sorry left

Closed the existing hole `AlgebraicGeometry.exists_quasiFinite_polynomial_chart` by reduction.
Proved the new intermediate theorem `AlgebraicGeometry.exists_fiber_dimension_nat` outright.
The only added and remaining hole is `AlgebraicGeometry.exists_quasiFinite_polynomial_chart_data`,
node `lem-sbc-quasi-finite-polynomial-chart-chart`. This is a decomposition: one existing hole
closed and one added, so the delivery claims no net hole reduction. The target still depends
on `sorryAx` through that chart theorem. There are no holes in definitions.

## No longer needed

No original imports were removed: they are all needed by the preserved target statement.
The target node's original direct proof dependencies are no longer used directly:
`def-weil-affine-spectrum`, `def-pc-scheme-fibre`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-dimension-at-point-local-ring-trdeg`,
`lem-weil-pbc-quasi-finite-over-polynomial-algebra`,
`lem-weil-pbc-spec-localization-away-basic-open`,
`def-nagata-relative-affine-space`, `def-sbc-locally-finite-presentation`.
The fibre-product, polynomial-algebra, and localization nodes are retained in the chart
subproblem's proof plan. The definition nodes remain statement dependencies; no modules
are claimed pruned. The old dimension-at-point/local-ring/trdeg route is replaced by the
upstream finite-type global dimension bound and the elementary local dimension inequalities.

## Where the brief, the DAG or earlier work was wrong

The first worker left a fibre-dimension hole that the upstream library can close. Its main
signature renamed `hy` to `_hy`; I restored `hy` and suppressed only this theorem's linter
warning. The original node's proof metadata was not updated, and the new holes' docstrings
were only summaries. I updated the proof metadata and expanded both proof explanations.
The purported statement-change record contained no change and was removed.

## New nodes

`lem-sbc-quasi-finite-polynomial-chart-dimension`: finite natural-valued local dimension of
an affine finite-type fibre, now proved from the upstream dimension theorem.

`lem-sbc-quasi-finite-polynomial-chart-chart`: the prescribed-dimension chart construction,
still open, with a complete natural-language proof from Tag 00QE, the existing ring-level
polynomial chart theorem, and affine localization transport. No change records are needed.

## Second reading by C4

1. Compared every delivered module with the repository. The main theorem's existing signature
   is byte for byte unchanged. The two nested modules are new. No definition or existing
   declaration statement changed, and the new imports are proof-only.
2. Compiled all three modules locally. Inspected every delivered declaration for prohibited
   constructs and hollow definitions. Only the chart-data theorem remains `sorry`. Axiom
   checks show the dimension lemma uses only the permitted standard axioms; the main theorem
   additionally uses `sorryAx` through the explicitly reported chart-data theorem.
3. Checked the split statements against Stacks Tags 00QE and 00RH and searched independently
   using LeanFinder, Loogle, the Mathlib grep service, and local rg. LeanSearch
   was also attempted but returned an internal server error. Found and used the upstream
   finite-type dimension theorem to close the dimension subproblem. The existing ring theorem
   `exists_quasiFinite_over_polynomial_algebra` is the input to the remaining scheme transport,
   not an exact match. Both split statements have docstring arguments and matching nodes.
   Empty X has no quantified point; dimension zero gives a quasi-finite neighbourhood over T;
   for positive dimension the polynomial variables have precisely the supplied cardinality.
   Neither subproblem has the target's hypotheses and conclusion: the dimension subproblem
   only proves finiteness, and the chart subproblem assumes a dimension equality and only
   constructs the corresponding chart.
4. The proof extracts the fibre dimension, applies the prescribed-dimension chart result,
   and combines the witnesses. It preserves the unit route; `sk-prop-normal-form.realized`
   is unchanged and this node does not realize a unit statement or step. Original imports
   are signature dependencies. The no-longer-directly-used nodes are listed above; no module
   is claimed pruned.
5. Updated the target node to the two actually used declarations; the dimension node records
   its completed proof and the chart node records the affine identification, existing
   polynomial-ring theorem, and localization transport. New nodes have creation, source,
   search, blueprint, unit, and verbatim Lean statement records.

Second reading changed: restored the original binder, localized its warning suppression,
proved the dimension lemma, expanded proof docstrings, corrected DAG dependency metadata,
removed the spurious change record, and rewrote this report to count the decomposition honestly.
