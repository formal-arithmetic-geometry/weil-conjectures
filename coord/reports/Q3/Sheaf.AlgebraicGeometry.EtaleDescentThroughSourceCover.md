## What changed

Filled `AlgebraicGeometry.Etale.of_comp_of_surjective_etale` in
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover` with the existing four-step
argument, preserving its signature and all public imports. Smoothness descends by
`Smooth.of_comp_of_flat_of_surjective`. For a point lifted through `p`, the existing
flat composite fibre dimension formula and the two étale zero-dimension results give
zero fibre dimension for `h`. The existing étale-neighbourhood theorem supplies a
cover, and `IsZariskiLocalAtSource.of_iSup_eq_top` concludes.

Updated the node's second step, proof dependencies, and proof origin to use Mathlib's finite-presentation-to-finite-type instance.
No new statements, definitions, public interfaces, or consumer adaptations.
Validation: the final module compiled through `lcompile.py` in 2.8 seconds
with exit code 0 and no compiler diagnostics.

The proof makes no nonemptiness assumption: the family indexed by points covers
also when `X` is empty.

Searches used LeanFinder, Loogle, the prescribed grep service, and direct searches
of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`. The hits for `Etale.of_comp`
cancel the second morphism to conclude étaleness of the first, and the descent
instance is for target base change; neither proves the present assertion.
Read Stacks `lemma-etale-etale-local-source` (036W) and
`lemma-etale-permanence-two` (02K6); the latter's local-finite-presentation
hypothesis is supplied here by smoothness descent, as its footnote explains.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.of_comp_of_surjective_etale`
(node `lem-trf-etale-descent-through-source-cover`).
One of one original holes closed; zero holes added; zero split off;
zero `sorry` remain in the delivered Lean module. The proof uses the existing
library dependencies with their existing proof status; no dependency proof is
replaced or altered.

## No longer needed

Removed redundant private imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`

The needed smoothness, finite-type, finite-presentation, and locality APIs are
already available through the retained imports. In particular, Mathlib's instance
supplies the elementary finite-presentation-to-finite-type implication, so the
proof no longer needs the node dependencies
`lem-weil-pbc-affine-opens-basis` or
`lem-weil-pbc-lfp-affine-opens-finite-presentation`.
These are Mathlib leaves; no project Lean module is withdrawn or globally pruned.
All four existing approved tool dependencies are retained. The unit's statement
and proof steps remain intact; this only shortens an elementary node-level step.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The expanded affine-cover argument in the
old second step duplicated an existing Mathlib instance. The proof uses that
instance directly. No return or rework entry names this item.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
