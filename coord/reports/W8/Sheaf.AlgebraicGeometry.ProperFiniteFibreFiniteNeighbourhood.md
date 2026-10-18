## What changed

Proved `AlgebraicGeometry.exists_open_isFinite_restrict_of_isProper_of_finite_fibre`
in `Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood` by applying
Mathlib's `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`
to `f`, `s`, and `hs`. Added its proof-only import
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`; preserved all existing public imports,
the declaration signature, and its visibility. Updated the item's DAG proof to cite
`lem-trf-proper-finite-fibre-finite-near`, already attached to that exact Mathlib theorem.
No definitions or statements changed, and no consumer adaptations are needed.

The source was checked in `literature/stacks-project/coherent.tex`,
`lemma-proper-finite-fibre-finite-in-neighbourhood` (Tag 02OH), and Mathlib's
Tag 02UP theorem at `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:406`.
The latter has identical data and conclusion and needs no Noetherian hypothesis.
The unit record `sk-thm-picard-rr` has no realized steps at this node;
the route change is below the unit level.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_open_isFinite_restrict_of_isProper_of_finite_fibre`
(node `thm-sc-proper-finite-fibre-finite-neighbourhood`).
No holes remain in the item; no holes or new declarations were added.
This is a proof, not a decomposition. The direct application compiled through
`lcompile.py`; the final pruned version and the axiom probe are checked by delivery.

## No longer needed

Removed these seven proof-only imports:

- `Sheaf.AlgebraicGeometry.FiniteDiscreteFiber`
- `Sheaf.AlgebraicGeometry.FiniteIffProperFiniteFibres`
- `Sheaf.AlgebraicGeometry.ProperBasic`
- `Sheaf.AlgebraicGeometry.QuasiFiniteIffFiniteFibres`
- `Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
- `Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen`
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`

The proof no longer uses any of the seven old declared proof dependencies:
`pqf-lem-proper-basic`, `pqf-lem-locqf-fibre-discrete`,
`lem-sc-quasi-finite-points-open`, `lem-pc-proper-base-change`,
`pqf-lem-qf-locqf-qc`, `pqf-lem-qf-finitefibres`, and
`thm-pqf-finite-iff-proper-finite-fibres`.
Mathlib's complete neighbourhood theorem supplies their combined conclusion directly,
so separate applications, the custom quasi-finiteness interface, and its open-locus
hole are unnecessary for this item. Removed the obsolete top-level `tool_uses`
approvals for the five old pqf tools (including their duplicate entries).
These nodes and modules may still have other consumers; no global unreachability
is claimed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's 2026-10-10 search missed the exact Mathlib Tag 02UP theorem.
The existing node `lem-trf-proper-finite-fibre-finite-near` now records it.
The original multi-step plan is valid but unnecessarily reconstructs a theorem
already proved in Mathlib. The proof needs no new intermediate theorem, and the
item's locally Noetherian assumption remains untouched.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
