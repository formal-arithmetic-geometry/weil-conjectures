## What changed

Completed the proof of
`AlgebraicGeometry.ProEtale.CondensedRing.derived_open_square_restriction`
in `Sheaf.Paper.DerivedOpenSquareRestriction`. All four existing public definitions
and the theorem signature are unchanged (compared verbatim).

The proof uses the declared coefficient-compatible open-square comparison, proves
invertibility and termwise normalization of the recorded open units from existing
fully faithful linearization and exact-derived adjunction APIs, and constructs rho
by `conjugateIsoEquiv` for the two composite adjunctions. Proved private helpers
identify its action with the five prescribed Hom bijections and identify the open
mate. Existing exact-derived and conjugation shift instances prove all shift clauses.
The comparison chosen from the scalar-comparison theorem is determined uniquely:
its inverse has a specified image under an injective adjunction Hom equivalence.
Thus no arbitrary mathematical data are chosen from mere existence.

Added private proof imports:

- `Sheaf.Paper.CondensedOpenSquareScalarComparison`;
- `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`;
- `WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction`;
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction`.

Updated the item's node proof, proof dependencies and proof origin to describe
this route. No public interface, source-library module or other worker's module
was changed. No new public declarations or nodes were added. All Lean lines have
at most 100 characters. The unit's open-restriction/derived-direct-image route is kept.

The final item compiled through `lcompile.py` with no errors or warnings
(37.4 seconds).

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.derived_open_square_restriction`
(node `lem-sfb-derived-open-square-restriction`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0. Split off: 0.
All nine private helper theorems are proved. No definitions contain holes.
The existing imported theorem
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_square_scalar_comparison`
remains a declared geometric input; its hole is not added by this delivery.

## No longer needed

The direct dependency `lem-sfb-condensed-open-adjunction-localization`
(`Sheaf.AlgebraicGeometry.CondensedOpenAdjunctionLocalization`) is unnecessary: existing
fully faithful linearization, exact-derived unit and shift theorems prove the
required assertions for the actual recorded adjunctions. Its module is not imported.
This removes a dependency edge; no module is withdrawn or claimed globally unused.

Removed these private imports:

- `Sheaf.Paper.CartesianCoefficients`;
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`;
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates`;
- `Sheaf.CategoryTheory.ExactDerivedComposition`;
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`;
- `Sheaf.CategoryTheory.SheafTensor`;
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`;
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`.

The homotopy adjunction is already publicly available from the derived adjunction
API and is still used. The scalar comparison retains the geometric coefficient
and base-change work internally; its public imports also expose several of these
interfaces. Removing redundant direct imports does not withdraw their declarations.
The parent does not separately invoke `cartesianCoefficients`, a tensor theorem,
quasi-compactness of the projection, or a constructed resolution theorem. Accordingly
`sk-prop-sfb-cartesian-coefficients`, `sk-def-sfb-sheaf-tensor`,
`lem-pc-quasi-compact-base-change` and `sk-def-sfb-derived-categories` are no longer
direct proof dependencies. The ambient exactness, tensor and resolution instances
remain available from existing public interfaces, and the scalar comparison retains
its own dependencies. The existing top-level approved tool list is preserved;
these underlying tools have not been globally pruned.

A separate Yoneda construction and two-sided inverse calculation are unnecessary:
Mathlib's proved `conjugateIsoEquiv` supplies the natural isomorphism. Its counit
formula proves the requested Hom characterization, and the existing conjugate shift
instance proves its shift square.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The earlier plan suggested an additional open-adjunction
localization theorem and an explicit representing-map construction. Both can be
replaced by existing proved APIs without changing the assertion or the unit route.
The original eight-step docstring is replaced by the six steps actually formalized.
The genuine scalar-compatible open base-change input remains a separate dependency.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
