## What changed

Completed `groupCohomology.inflation_periodic` in
`Sheaf.GroupTheory.CyclicInflation`, retaining its statement and docstring.
Retained the proof-only import of
`Sheaf.RepresentationTheory.ResolutionInflationComparison` and added the proof-only
import `Mathlib.GroupTheory.Coset.Basic`.

The proof constructs the quotient map of regular representations and counts its
fibers to show that the larger norm maps to `r` times the smaller norm. Multiplying
this quotient in degree `s` by `r ^ (s / 2)` gives an augmentation-preserving chain
map. The existing resolution comparison theorem identifies its induced cochain
map with inflation. Evaluation at the identity gives the required scalar formula.
A zero degree component induces a zero map on homology, yielding vanishing in
degrees at least two when `r` annihilates the coefficient module. The proof also
identifies the representation's lifted-integer module structure with the canonical
integer action used in the displayed heterogeneous equality.

Retained the earlier sandbox proof attempt and repaired its norm simplification,
cochain evaluation, heterogeneous equality conversion, and linear-map extensionality.

## Proved and sorry left

Closed one hole: `groupCohomology.inflation_periodic`
(node `det-base-field-cd-inflation`). Added zero holes and split off zero statements.
No `sorry` remains in the delivered module.

The proof uses the existing named theorem
`groupCohomology.resolution_inflation_comparison`
(node `lem-sfb-resolution-inflation-comparison`), which remains `sorry` in its own
module. It is an existing declared dependency, not a new hole in this delivery.

## No longer needed

None. Both declared proof dependencies remain necessary:
`lem-sfb-cyclic-periodic-resolution` supplies Mathlib's periodic resolutions and
evaluation isomorphisms, and `lem-sfb-resolution-inflation-comparison` identifies
the constructed comparison with inflation. No imports, nodes, or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The retained sandbox had four local Lean proof
errors, now repaired. The proof follows all four existing DAG steps and preserves
the unit's periodic-resolution route. No signatures or existing definitions change.

Validation: the retained module was rechecked against the current source, DAG, and
unit route and compiled without warnings through `lcompile.py` in 4.6 seconds. The source-level delivery comparison reports no interface changes,
no changed public statements, no added public declarations, no changed public
imports, one closed hole, and zero remaining or added holes.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
