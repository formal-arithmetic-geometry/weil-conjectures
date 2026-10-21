## What changed

Completed the zero-hole retirement of
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation` listed in
`coord/retire-items.tsv`. The module is withdrawn in `deleted.txt`. Its node
`lem-sbc-geometric-strict-henselization-local-presentation` now points to the complete
upstream `AlgebraicGeometry.Scheme.strictHenselizationRing_local_presentation`.
No upstream file is modified.

Adapted the unclaimed
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation` without
changing its theorem signature, visibility, or existing docstring. The proof checks the
two structural maps on a representative colimit leg, applies the upstream presentation,
and transports the local-base action and the universal pointed-etale cocone back through
the canonical ring isomorphism. It constructs the quotient action explicitly by quotient
and localization lifts, then applies the upstream localized-divisor theorem. Its private
proof imports now use the upstream twins; its public structural-map import uses the
upstream owner to avoid the duplicate compatibility declaration.

Switched the private local-presentation import of
`Sheaf.TraceFormula.CoordinateMaximalBranchStratum` to the upstream twin. Its theorem
and unfinished proof are unchanged. Updated the two existing DAG proof records to
match the retained upstream proof and the consumer's explicit transport. The mathematical
statements, dependency lists, parent edges, and unit route are unchanged.

Change record:
`coord/changes/N3-strict-henselization-local-presentation-retirement.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Item holes remaining: 0.
Split-offs: 0. This is a retirement repair, not a proof-hole closure or decomposition.

The retained upstream local-presentation theorem is proved. The adapted
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_presentation`
(node `lem-sbc-strict-hensel-divisor-quotient-presentation`) remains completely proved,
as does its new private `comparison_base` helper. Neither has any sorry dependency:
independent axiom checks list exactly `propext`, `Classical.choice`, and `Quot.sound`.

The only sorry left in a delivered Lean consumer is the unchanged
`AlgebraicGeometry.Scheme.IdealSheafData.coordinate_maximal_branch_stratum`
(node `lem-trf-nc-coordinate-max-stratum`). It was present before this retirement;
its proof remains exactly `by sorry`. No other hole is added or moved.

Validation: both changed consumers compile together through `lcompile.py --all`
without warnings (8.6 and 5.5 seconds). The direct importer
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`
compiles unchanged against the sandbox artifacts (11.0 seconds). An explicit probe
checked the axioms of both the retained local-presentation theorem and the adapted
divisor-quotient theorem. All delivered Lean lines are at most 100 characters.

Edge cases: the proof adds no regularity, Noetherianity, or nonzerodivisor assumption.
For f = 0, the quotient/localization construction still works. A unit f is excluded
by the original nonunit hypothesis. A field base and nonreduced base rings remain
covered; the canonical ring isomorphism preserves nilpotents. No geometric point over
the zero ring exists. The separable closure is a concrete `SeparableClosure`, and both
algebra actions are explicit ring-hom constructions.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation`.
Its public compatibility theorem is no longer needed as a declaration: the single
consumer performs the canonical transport in its existing proof. The trace-formula
consumer retains the mathematical dependency by importing the upstream twin.

Removed Sheaf proof imports from the divisor consumer:
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation` and
`Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient`, replaced by their
upstream twins. Its old public import of
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` is replaced by the upstream
owner. Those other Sheaf modules are independently claimed (M1 and M4 respectively)
and are not changed or withdrawn by this packet. No mathematical dependency node is
pruned: all four local-presentation dependencies remain in the retained upstream proof,
and both divisor-presentation dependencies remain used. No source-library declaration
is removed or weakened.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief described an unfinished statement, but this dispatch is a
zero-hole retirement item (`coord/queue.tsv` and `coord/retire-items.tsv`, row for the
item). B4 had restored a valid small-colimit bridge, so merely copying or recompiling
that module would leave the assigned retirement incomplete. The prior J3 retirement
failed because it did not adapt the live divisor-quotient consumer; this packet does.

The upstream theorem uses `strictHenselization` and `strictLocalizationToBase`;
the small-colimit consumer uses `strictHenselizationRing` and
`strictHenselizationStructuralMap`. These are related by a canonical isomorphism,
not definitional equality. The structural-map equation is proved before transport,
and the consumer's exact small-colimit statement stays unchanged. Loading the old
Sheaf structural-map import together with upstream LocalPresentation gives a duplicate
`strictHenselizationStructuralMap_eq` import error, so its public import must use the
upstream owner. Upstream `localized_divisor_quotient` takes a specified quotient prime,
separable closure, action and compatibility equation, rather than the old existential
Sheaf interface; the complete explicit construction in the adapted proof supplies them.

Searches through msearch (LeanFinder, Loogle, and grep) found no Mathlib strict
henselization presentation. Source search found the already proved upstream theorem,
its canonical colimit comparison, and the upstream quotient-action construction.
The proof reuses these existing results. No new node or unfinished split is needed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
