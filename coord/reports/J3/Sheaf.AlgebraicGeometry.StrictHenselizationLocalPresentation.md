## What changed

Completed the listed retirement in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation`.
The existing upstream module
`WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation`
retains `AlgebraicGeometry.Scheme.strictHenselizationRing_local_presentation`.
Its proof first establishes the general open-affine-chart presentation and then
specializes to the identity chart, using faithfulness of Spec to identify the
given structural ring map. The duplicate Sheaf module is withdrawn via
`deleted.txt`; no upstream source is changed.

Migrated the sole current Lean importer,
`Sheaf.TraceFormula.CoordinateMaximalBranchStratum`, by replacing only its private
import with the upstream module. Its statement, docstring and existing proof are
unchanged. The live upstream divisor-quotient presentation already imports and
applies the retained theorem. The archived Sheaf divisor-quotient module remains
quarantined; its absence is not treated as a withdrawal.

Retained node `lem-sbc-geometric-strict-henselization-local-presentation` and all
its incoming and outgoing mathematical dependencies. Updated only its Lean
attachment and proof description/origin to the existing upstream proof. The
natural-language statement, statement dependencies, proof dependencies and unit
route stay. The two colimit implementations have the canonical comparison
`smallStrictHenselizationColimitIso`; the upstream theorem includes every original
prime-localization, separable-closure, scalar-tower and structural-map clause.

Change record:
`coord/changes/J3-strict-henselization-local-presentation-retirement.md`.

## Proved and sorry left

This is a duplicate-module retirement, not a new proof or decomposition.
The item already had zero sorry declarations: original holes 0, holes closed 0,
holes added 0, remaining item holes 0, split-offs 0.
The retained upstream theorem
`AlgebraicGeometry.Scheme.strictHenselizationRing_local_presentation` has a complete
proof; it is preserved verbatim.

The adapted consumer retains its one pre-existing sorry:
`AlgebraicGeometry.Scheme.IdealSheafData.coordinate_maximal_branch_stratum`
(node `lem-trf-nc-coordinate-max-stratum`). No new sorry is introduced anywhere.

Validation: the adapted consumer compiled remotely with no warnings in 2.7 seconds.
The change to its source is exactly one private import line.
A separate remote check imported the retained upstream theorem, printed its type,
and ran `#print axioms`: exactly `propext`, `Classical.choice`, `Quot.sound`.
This confirms that the retained proof has no transitive sorry dependency.
The required delivery dry run passed compilation and preflight at `287eb233fa`.
It is classified CODEX for the retirement, node attachment change, change record
and consumer migration. No target or source-library declaration is edited.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation`.
Its duplicate declaration is supplied by the upstream module of the same basename.
Removed the consumer's private import of the withdrawn module and replaced it
with that upstream import.

The withdrawn module's imports were
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`,
`WeilConjectures.RingTheory.IsStrictHenselization`,
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`, and
`WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization`.
These cease to be edges from the withdrawn module. The mathematical ingredients
remain in the retained upstream proof; none of their modules or DAG nodes is
claimed pruned by this delivery. No other module is withdrawn.

All actual DAG parents continue to cite the same node, now attached to the
upstream theorem: `lem-sbc-strict-hensel-divisor-quotient-presentation`, `lem-trf-nc-coordinate-max-stratum`, `lem-per-complete-local-branch-approximation`, `lem-per-trait-affine-lefschetz`.
This includes unfinished and quarantined parents. The existing unit realization
is unchanged, and no parent needs the duplicate implementation.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a module with a proof hole or a repair. The
current item instead appears in the retirement queue, and its current Sheaf proof
already contains zero holes. The retirement table lists two historical consumers;
only the trace-formula consumer currently imports the Sheaf module. The Sheaf
divisor-quotient presentation is quarantined, while its live upstream counterpart
already uses the upstream presentation. Neither archive nor upstream declarations
are removed or weakened.

The old Lean attachment pointed to the duplicate small-representative-colimit
implementation. The upstream theorem uses the canonical affine-neighbourhood
colimit and structural map, with the same geometric and algebraic meaning. The
node is retained and its attachment now names that implementation.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
