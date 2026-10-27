## What changed

Filled the proof of `Module.length_eq_nat_of_support_subset_maximalIdeal`. The proof uses
an annihilator quotient: support identifies every prime of the quotient with the maximal
ideal, so Mathlib's zero-dimensional Noetherian-to-Artinian theorem applies. The finite
module is then Artinian over the quotient, and the surjective semilinear identity transfers
Artinianness back to `R`. Retained the existing public imports and added private proof imports of `Mathlib.RingTheory.HopkinsLevitzki` and
`Mathlib.RingTheory.Ideal.Quotient.Noetherian`.

## Proved and sorry left

Closed 1 of 1 holes: `Module.length_eq_nat_of_support_subset_maximalIdeal`
(node `lem-sc-generic-stalk-finite-length`). Added 0 holes; no `sorry` remains.
The finished module compiles through `lcompile.py`.

## No longer needed

The planned powers-of-the-maximal-ideal filtration and its dependencies
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`, `lem-weil-pbc-fg-ideal-radical-power`,
`lem-weil-pbc-noetherian-submodule-finite`, and
`lem-weil-pbc-length-additive-short-exact` are not used, and their obsolete `tool_uses` approvals were removed.
No Lean modules are withdrawn; these four nodes are Mathlib leaves.
No original imports were removed. Removed the trial redundant private import
`Mathlib.Algebra.Module.Torsion.Basic`, supplied by Hopkins-Levitzki.
No new DAG nodes were needed:
the other algebraic facts are direct Mathlib declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was valid but substantially longer than necessary. Mathlib already
contains the quotient zero-dimensional Artinian theorem, finite-module Artinian instance,
and semilinear Artinian equivalence, so the filtration route is pruned.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
