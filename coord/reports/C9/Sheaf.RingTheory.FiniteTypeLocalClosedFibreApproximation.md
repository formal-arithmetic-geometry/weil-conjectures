## What changed

Proved `Algebra.exists_finitePresentation_local_approximation_closedFibre` in
`Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation` from Mathlib. The statement,
universes, and hypotheses are unchanged. Updated the docstring and existing node's
proof, proof dependencies, and proof origin to match the implementation. Added
the proof import `Mathlib.RingTheory.PrincipalIdealDomain` for the instance that
a field is Noetherian. The existing proof imports for prime localization and
Noetherian localizations are used.

The proof evaluates a polynomial algebra on the finite set furnished by
`Algebra.essFiniteType_iff`, localizes at the inverse image of the maximal ideal,
and proves the resulting map onto B is surjective using the unit denominators.
The closed fibre is Noetherian by `Algebra.EssFiniteType.quotient_map` and
`Algebra.EssFiniteType.isNoetherianRing`. Choose finitely many polynomial kernel
elements generating the kernel image in that fibre, quotient by their localized
ideal, and use the quotient-localization instance to obtain the finite-presentation
witness. Equality of ideal inverse images proves bijectivity of the specific
closed-fibre quotient map.

All witnesses are local constructions inside a theorem proof. No data definition
chooses an arbitrary witness from an unproved existence theorem. The proof applies
also to an empty set of algebra generators, an empty set of kernel relations,
a field base, and a non-Noetherian local base: only the closed fibre is assumed
Noetherian, and this is proved. The source typo claiming finite presentation in
the opening sentence is not used.

Searches: LeanFinder for a polynomial-localization presentation of an essentially
finite type local algebra; Loogle `Algebra.EssFiniteType, IsLocalRing`; grep of the
localization library for surjective existence results; direct searches in Mathlib,
Sheaf, and WeilConjectures. No matching approximation theorem was found.

## Proved and sorry left

Closed 1 hole:
`Algebra.exists_finitePresentation_local_approximation_closedFibre`
(node `lem-sfb-finite-type-local-closed-fibre-approximation`).

Zero holes remain in the item; zero holes added; zero statements split off.

Validation: `lcompile.py` compiled the complete proof without errors or warnings
(11.2 seconds). `#print axioms` reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. The diagnostic command was removed from the delivery source.

## No longer needed

Removed the unused public import `Mathlib.RingTheory.Localization.Algebra`.
All eight declared DAG dependencies remain mathematically used, through Mathlib
results. No Sheaf or WeilConjectures dependency module is imported, and no DAG
node or project module is withdrawn or pruned.

The explicit identification of the closed fibre with a localized polynomial ring,
the separate clearing of denominators of localized relations, and the choice of
a quotient prime are unnecessary: choose finite polynomial kernel generators
directly, and use Mathlib's essentially-finite-type quotient instance and general
quotient-localization instance. The revised node records these shorter steps.

## Where the brief, the DAG or earlier work was wrong

Change record: `coord/changes/C9-finite-type-local-approximation-unused-import.md`.
The downstream script found zero Lean importers, so removing the unused public
import requires no consumer adaptations.

No statement correction was needed. The original plan is valid but can use the
shorter Mathlib APIs noted above. The source's opening “essentially of finite
presentation” is a typo for the finite type hypothesis, already noted by the DAG
review; the implementation uses precisely the stated finite type hypothesis.

The blueprint unit's route is preserved; this item is an auxiliary algebraic
approximation in the unchanged fibrewise-flatness route. No target statement,
definition, or consumer was changed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
