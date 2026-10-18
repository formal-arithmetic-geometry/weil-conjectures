## What changed

Proved `CategoryTheory.BigradedExactCouple.finiteCocone_limitCycles` without changing its
signature, following the existing two-step DAG plan. The proof uses the proved
`pageCouple_image_prefix` declaration, inducts on the finite cycle projections, and
uses the upper zero tail to kill the corresponding monomorphic D inclusion. The GLB
property and the transported exactness equality give the forward inclusion;
`g_factors_limitCycles` gives the reverse inclusion.

The only proof imports retained are
`WeilConjectures.CategoryTheory.DerivedCoupleExact` and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`. The public import is unchanged.
No definitions, public signatures, node statements, or dependency routes changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.BigradedExactCouple.finiteCocone_limitCycles`
(node `lem-sp-finite-cocone-limit-cycles`).

Proved 1 of 1 sorries. Added 0 holes; split off 0 statements. There are no sorries
left in the delivered module. The named proof dependencies used here are already proved.
The final single-file compile passes without warnings.

## No longer needed

Removed these redundant proof imports:

- `Sheaf.CategoryTheory.DerivedCoupleExact`: retired re-export of the upstream module
  that the proof imports directly.
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`: the proof does not use
  its abelian lattice lemmas.
- `WeilConjectures.CategoryTheory.ExactCouple`: its public declarations are already
  available through the unchanged public convergence import.
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`: already re-exported by the
  unchanged public `Sheaf.CategoryTheory.ExactCoupleConvergence` import.

All three declared proof-dependency nodes remain used:
`lem-sp-derived-couple-image-prefix`, `def-sp-exact-couple`, and `def-sp-convergence`.
No dependency node is pruned. No general finite-cycle formula or additional helper
module is needed; the projection induction proves the required consequence directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing plan could be completed from
its stated declarations without another split. The local Stacks homology source was
read at the exact-couple formulas and boundedness discussion. The unit has no
realized statement or proof-step nodes bypassed by this argument.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
