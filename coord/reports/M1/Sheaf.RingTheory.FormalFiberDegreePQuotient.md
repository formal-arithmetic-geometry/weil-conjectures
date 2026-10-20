## What changed

Completed the retirement item listed in `coord/retire-items.tsv`:
withdraw `Sheaf.RingTheory.FormalFiberDegreePQuotient` through `deleted.txt` and redirect
`new-lem-weil-pbc-degree-p-quotient-component` to
`WeilConjectures.RingTheory.FormalFiberDegreePQuotient`, declaration
`MvPowerSeries.nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct`.
The official theorem has the exact same signature and proof after renaming the declaration;
this was checked by comparing the complete theorem text. Its proof follows the existing DAG
route, including the zero-algebra case. No upstream files change.

The official theorem and its existing official consumer
`WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation` compile
individually through `lcompile.py` (4.3 s and 16.5 s). The original Sheaf theorem also compiled
before withdrawal (4.1 s). The official theorem's axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Change record: `coord/changes/retire-formal-fiber-degree-p-quotient.md`.

## Proved and sorry left

Retirement of an already proved duplicate: 0 of 0 holes closed, 0 holes added, 0 split off.
No `sorry` remains in the retired item; no Lean theorem or definition is added.
The official replacement theorem is fully proved and uses only the three allowed axioms.
This is module pruning, not a new proof or a decomposition.

## No longer needed

Pruned module: `Sheaf.RingTheory.FormalFiberDegreePQuotient`, including the duplicate declaration
`MvPowerSeries.FormalFiberDegreePQuotient`.
Its four Mathlib imports disappear with the module:
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
`Mathlib.RingTheory.TensorProduct.Basic`, `Mathlib.Algebra.Polynomial.Basic`, and
`Mathlib.RingTheory.Ideal.Quotient.Defs`. The official twin still uses these Mathlib modules;
no claim is made that they leave the targets' closure.
No mathematical dependency or DAG node is pruned: the existing node is retained and points
to the official theorem, with the same statement and proof steps.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed module, but this queue entry is explicitly
kind `retire` and the module has zero holes. Its official twin already provides its full
result under a different declaration name; the inventory's API difference is just that
rename. The inventory's former Sheaf consumer is already retired, while the remaining
official consumer already imports and calls the official theorem. Hence no consumer edit
is needed. A repository-wide search found no remaining Lean import or use of the old
module/declaration outside the module being withdrawn.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
