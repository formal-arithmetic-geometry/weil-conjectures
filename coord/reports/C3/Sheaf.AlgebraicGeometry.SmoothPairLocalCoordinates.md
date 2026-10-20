## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.Scheme.Hom.exists_etale_smooth_pair_coordinates`
with a complete Lean argument from local regular equations and two separate source arguments.
The proof explicitly shrinks the coordinate chart, pastes the pullback squares, proves the
restricted closed chart etale by base change, and transports the generated ideal and weak
regular sequence through the open-immersion section-ring isomorphism. Existing signatures
and the concrete `AffineSpace.zeroLastCoordinates` definition are unchanged.

The two new modules isolate the first and second parts of the Stacks 0FUE proof. Neither is
the original theorem renamed: coordinate lifting assumes prescribed regular equations and
requires no ambient smoothness, and its ambient map need not be etale; the second is an
etaleness criterion for a given map and constructs no coordinates. Their proofs remain open.
This is a decomposition, not a net reduction of holes.

Validation: all three sandbox modules compile together through lcompile.py. The open-immersion
transport originally triggered expensive elaboration of an implicit ring-hom coercion;
explicit section-ring types and `.toRingHom` resolve it without changing definitions or limits.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.Hom.exists_etale_smooth_pair_coordinates`
(node `lem-pur-smooth-pair-local-coordinates`), proved relative to its named prerequisites.
The assigned module has zero remaining `sorry`.

Added 2 holes, each in a new public named theorem:

- `AlgebraicGeometry.Scheme.Hom.exists_coordinate_lift_of_regular_equations`
  (`lem-pur-smooth-closed-coordinate-lift`, SmoothClosedCoordinateLift.lean).
- `AlgebraicGeometry.Scheme.Hom.exists_etale_open_of_regular_coordinate_fibre`
  (`lem-pur-etale-near-regular-coordinate-fibre`, EtaleNearRegularCoordinateFibre.lean).

No definition contains `sorry`. The regular-equations prerequisite already had its own hole;
this delivery does not change it. The delivered decomposition closes one hole and adds two.

## No longer needed

Removed direct proof imports from the assigned module:

- `Mathlib.RingTheory.Smooth.Flat`.
- `Mathlib.RingTheory.KrullDimension.Regular`.
- `Mathlib.RingTheory.Kaehler.TensorProduct`.
- `Mathlib.RingTheory.LocalRing.Module`.
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`.
- `WeilConjectures.RingTheory.SmoothFibreRegularLocal`.
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`.
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`.
- `WeilConjectures.RingTheory.Etale.LocalDimension`.
- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`.
- `WeilConjectures.RingTheory.MiracleFlatness`.
- `WeilConjectures.RingTheory.FlatOfFlatClosedFiber`.
- `Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion`.
- `Sheaf.RingTheory.RelativeRegularEquationsBaseChange`.

The old direct proof dependencies for choosing an etale chart and lifting its coordinates
now belong to `lem-pur-smooth-closed-coordinate-lift`; the dimension, flatness and differential
arguments now belong to `lem-pur-etale-near-regular-coordinate-fibre`. They are not claimed
pruned from the transitive closure. No mathematical node or module is globally pruned by
this decomposition. All seven obsolete direct `tool_uses` entries of the original node
are removed; the new criterion retains their mathematical uses in its proof steps.
The normal-form import was also removed after checking the proof does not use it directly.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair. The declared dependencies provide the algebraic
inputs, but do not supply the scheme-level coordinate lifting or the passage from local
algebraic flatness and differentials to a neighbourhood of the specified coordinate map.
These are separate arguments in Stacks 0FUE, now stated with exact Lean interfaces.
The alternative differential criterion in EtaleAtPointFromDifferentials works over a field;
it does not directly close this item's arbitrary-base argument.

Edge checks: if the equation list is empty the coordinate inclusion is the identity and
regularity imposes no injection conditions; the criterion becomes etaleness of h on its
whole given coordinate fibre. For a=0 the closed chart is etale over the base and no first
coordinate lifts are needed. Empty Y makes the pointed statements vacuous. Affine opens
missing the closed subscheme can have zero quotient, which is why weak regularity rather
than regularity is asserted on all affine opens. No arbitrary witness from an unproved
existence theorem is used to define an object.

## New nodes

`lem-pur-smooth-closed-coordinate-lift` is the chart-lifting portion of Stacks 0FUE:
choose the smooth closed chart, lift functions through the affine quotient and append
the given regular equations. It has its own source, explicit proof, searches, and Lean
statement in `lean/Sheaf/AlgebraicGeometry/SmoothClosedCoordinateLift.lean`.

`lem-pur-etale-near-regular-coordinate-fibre` is the local flatness and etaleness argument
of Stacks 0FUE. Its hypotheses fix the map and its etale regular coordinate fibre; its
conclusion only supplies an etale neighbourhood for that map. Its separate module is
`lean/Sheaf/AlgebraicGeometry/EtaleNearRegularCoordinateFibre.lean`. Its proof records the
fibre dimension computation, miracle flatness, flatness fibre criterion and Nakayama.

No change records are needed: no existing definition, signature or visibility changed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
