## What changed

Proved `AlgebraicGeometry.Scheme.Modules.coherentRawScalarRestriction` with its
original statement. Raw evaluation transports the scalar action to derived
cohomology. The coefficient scalar square gives the cohomology scalar square,
and cancellation of the raw comparison isomorphisms gives the required identity.
Raw restriction is identified by cancelling the two existing fixed-resolution
naturality and restriction comparisons.

Three new auxiliary modules provide proved interfaces for coefficient composition,
cohomology pullback naturality, and the raw evaluation formula.
The natural transformation has the original raw pullback as its explicit component,
with a proved component formula. An abstract categorical square argument takes
this formula as input, so naturality avoids a large rewrite of concrete expressions.
A structure with generic category and object parameters retains the prescribed
cohomology actions, pullback, their formulas and their commutation law. Its data
are explicit maps, and its formulas recover the original native maps. Generic
parameters keep its record declaration independent of concrete cohomology objects.
No existence theorem chooses an action.
No existing definition, target signature, adopted source declaration or unit route changes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.coherentRawScalarRestriction`.
Added zero holes. The new auxiliary theorems are proved:

- `AlgebraicGeometry.Scheme.Modules.restrictionScalar_comp_aux`;
- `AlgebraicGeometry.Scheme.Modules.coefficientPullback_square`;
- `AlgebraicGeometry.Scheme.Modules.raw_evaluation_formula_aux`;
- `AlgebraicGeometry.Scheme.Modules.complexCohomologyPullbackTransformation_app`;
- `AlgebraicGeometry.Scheme.Modules.normalizationCohomologyAction_formula`.

There are no `sorry`s in the delivered Lean files and no split obligations.
Existing declared resolution comparison theorems are used as intended in stage 3;
this does not assert that all transitive dependencies are already sorry-free.

## No longer needed

The originally planned `lem-weil-pbc-cohomology-pullback-functorial` is not used:
only coefficient naturality of pullback is needed, not its composition law.
`WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` is not imported.

`lem-weil-pbc-raw-restricted-class-normalization` is also unnecessary for this proof.
Cancel the two existing fixed-resolution comparison equations directly. The proof
does not import `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization`. Its
independent class-map and sheafification conclusions are not used here; supporting
declarations remain available through existing imports. All existing modules and
adopted declarations remain in the library for other consumers. No module is
withdrawn, and no global pruning claim is made for a module still used elsewhere.

The main module imports the chart-square construction privately. Only the
coefficient composition auxiliary module needs `UnitStructureCoefficientIso`. Exploratory imports were removed where
unused. The generic pullback construction imports only the original raw-cohomology
module and spells out the same global-sections comparison, so it exports no
additional derived shift instance. The assigned module retains its original public import.

## Where the brief, the DAG or earlier work was wrong

The assigned statement and mathematics are unchanged. The DAG's proposed pullback
functoriality dependency is stronger than required. The missing coefficient and
evaluation interfaces are proved here, not replaced by unproved versions of the
assigned obligation. The cohomology square is retained in a structure with generic
category and object parameters, with an explicit generic constructor.

## New nodes

`def-weil-pbc-single-cohomology-pullback` records the natural transformation with
its prescribed raw pullback components and the proved component formula.

`def-weil-pbc-restriction-scalar-endomorphism` records the scalar conjugate through
`coherentEtaleRestrictionIso`, with no existence choice.

`lem-weil-pbc-coherent-restricted-scalar-composition` records the coefficient scalar
square, proved by localization restriction and tensor-section semilinearity.

`lem-weil-pbc-coherent-raw-evaluation-formula` records the defining evaluation
formula, proved by coefficient naturality and cancellation of the evaluation isomorphisms.

`def-weil-pbc-single-cohomology-square` records the generic square data and its
explicit constructor retaining the prescribed maps and commutation law. It also
records the abstract categorical coefficient-square theorem and its explicit
retained-square construction.

`def-weil-pbc-normalization-cohomology-square` constructs this square with the
named raw chart groups as endpoints, using explicit named chart actions with their
proved single-complex formula. Its pullback is the prescribed normalization
restriction and its law is the generic coefficient-square argument instantiated
with the raw pullback transformation. This interface avoids
repeated conversion between named chart groups and expanded cohomology objects.

The assigned node's proof and dependencies follow these proved interfaces and the
two existing fixed-resolution comparison equations.

The proof-support command changes are recorded in
`coord/changes/G1-coherent-raw-scalar-proof-scope.md`. They change local elaboration
settings and a universe used only by a private helper; consumers need no adaptation.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
