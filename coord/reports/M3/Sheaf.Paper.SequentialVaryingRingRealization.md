## What changed

Proved `AlgebraicGeometry.Scheme.SequentialVaryingRing.realization` in
`Sheaf.Paper.SequentialVaryingRingRealization`. The proof uses Mathlib's
`DerivedCategory.right_fac` with a fixed target, recursively retains the prescribed
first representative, constructs all composite transitions, transposes the resulting
strict diagram of complexes, and checks every derived evaluation transition.

Replaced the ordinary compositor and unit supplied to `restrictionComp` and `derivedId`
by natural isomorphisms with identity components. Their signatures and mathematical
maps are unchanged; the explicit components avoid expensive comparisons of entire
restriction functors. Local instance priorities and reducibility attributes keep the
localization instances aligned. The transition recursion uses `Nat.leRec` with proved
identity, successor, composition, and localization equations. All helpers are private
and proved. No other module or target statement changes.

The exact delivery module compiled without warnings in 44.4 seconds after the
launcher resumed this worker. A profiling compilation of the full proof also passed
in 59.2 seconds. The definition changes and consumer checks are recorded in
`coord/changes/M3-sequential-varying-ring-proof-interface.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.SequentialVaryingRing.realization`
(node `lem-coef-sequential-varying-ring-realization`).

Proved 1 of 1 original sorries; added 0 sorries; 0 sorries remain in the item.
No statements were split off and no new nodes were introduced. Every private helper
has a complete proof. Existing imported declarations are used as the stage-3 brief
permits; their proofs are not replaced or weakened by this delivery.

## No longer needed

Removed the private imports
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction` and
`Mathlib.CategoryTheory.Localization.CalculusOfFractions`.

Removed `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` from this node's
proof dependencies and Step 1: the exactness instances already available from
`AdicCoefficientDatum` suffice. The separate ordinary-adjunction module is not needed
by this proof. The general right-fraction and quasi-isomorphism nodes remain part of
the argument, packaged by Mathlib's `DerivedCategory.right_fac`; no separate homotopy
quotient lifting is required. No unit statement or unit proof step is bypassed, and
no library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped on compile timeouts. These did not establish a tool
failure. The expensive definition comparisons are now avoided by componentwise
restriction comparisons, controlled local reducibility, and structural transition
recursion. Both the complete proof and its profiled version have compiled.

The old report described an unverified proof draft as complete; this report replaces
that claim with actual successful compilation. During resumed attempts the launcher
reset `.budget.start` from 1792670619.498367 to 1792730679.781977. The worker did not
edit that metadata and retained the original deadline. A later dispatcher resume
recorded `.budget.start = 1792773385.8472705`; the worker left this metadata untouched.
The launcher also paused and resumed the worker to shorten the compile queue.
Delivery attempts before that pause failed their compile gate and pushed nothing;
the exact module subsequently compiled cleanly after resumption.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
