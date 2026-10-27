## What changed

Proved `WeilConjectures.CompletionUnit.restricted_limit_acyclic` in
`Sheaf.Paper.CompletionUnitRestrictionAcyclicity`, without changing its statement.
Added proof imports of `Sheaf.CategoryTheory.RestrictedTowerResolutionAcyclicity`
and `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.

The private coefficient cone, additive vertical-slice equivalence, and equality
with the specified restriction functor follow the existing private construction in
`Sheaf.Paper.SequenceKInjectiveComparisonShifts`. This identifies the actual
coefficient restriction on objects, transitions, and morphisms via its uniqueness
characterization. Apply `SheafOfModules.RestrictedTowerResolution.acyclicity` to
the identity resolution of the transported K-injective complex and the given
replacement, then cancel the limit of the transport isomorphism. This is the
existing two-step DAG plan; no route or dependency changes are needed.

Only the item module changes. Its original public import and public declaration
signature are preserved. No shared definitions, source-library modules, or target
statements change. The server single-file compile passed in 13.9 seconds.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.CompletionUnit.restricted_limit_acyclic`
(node `lem-trf-completion-unit-restriction-acyclicity`).

No sorry remains in the item. Added 0 holes and split off 0 statements.
All private helpers are proved or constructed from actual coefficient projections.
The proof uses the existing general acyclicity declaration; it does not assume
that exact scalar restriction preserves K-injectivity. The independent site and
coefficient universes, unbounded complexes, and all original hypotheses remain.

## No longer needed

None. All existing declared proof dependencies are used:
`def-coef-ringed-sequence-site`, `lem-pur-system-ringed-sequence-site`, and
`lem-coef-restricted-tower-resolution-acyclicity`. No imports, nodes, or modules
are pruned. The larger `SequenceKInjectiveComparisonShifts` module is not imported:
only its private identification argument is reused in the item.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Library search found that
`SequenceKInjectiveComparisonShifts` already proves the required acyclicity as a
private helper; its construction gives the assigned proof directly using the
existing public general theorem. The existing DAG plan matches this argument.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
