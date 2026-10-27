## What changed

Replaced the hole in `exists_coherentHigherImageModuleAction` by an explicit
construction. Coefficient multiplication acts on cohomology: the proof establishes
the functor laws and additivity of `coherentEtaleMap` from its section formula,
and derives additivity of tensor pullback from its adjunction. A generic additive
functor constructor proves the module axioms without unfolding the concrete
coefficient. It constructs the cohomology module and restricts scalars along the
first projection. The abstract sheafification helper transports this module
through the fixed raw evaluation equivalence.

The lifted structure presheaf is a sheaf of rings. The canonical raw class map is
locally bijective because its sheafification lift is an isomorphism. Mathlib's
`PresheafOfModules.Sheafify.module` then constructs the action directly on the
actual higher-image sheaf. Its restriction formula and linear unit prove the two
required conclusions. No definition or existing public statement changed.

The remaining raw scalar restriction square is stated separately as
`coherentRawScalarRestriction`, with its own module and node. This square is
before sheafification, assumes no higher-image action, and asserts neither the
module laws nor the action on higher-image classes.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.Scheme.Modules.exists_coherentHigherImageModuleAction` by a
complete Lean reduction to the raw restriction square and the existing declared
normalization theorem. All private construction and assembly helpers are proved.
The item module has zero remaining `sorry` bodies.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.coherentRawScalarRestriction`, in
`Sheaf.AlgebraicGeometry.CoherentRawScalarRestriction`, node
`lem-weil-pbc-coherent-raw-scalar-restriction`.

This is one hole decomposed into one strictly smaller hole, not a net hole
closure. The new statement was checked on degree zero, identity arrows, zero
coefficients and empty charts. No data are chosen from a new unproved existence
statement.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
The item no longer needs `lem-weil-pbc-cohomology-pullback-functorial`,
`def-weil-pbc-coherent-etale-restriction` or
`def-weil-pbc-etale-cohomology-presentation` as direct proof dependencies. They
remain dependencies of the new raw scalar square, so none is claimed globally
pruned. No module is withdrawn. The module-sheafification interface and raw class
normalization remain in use. The proof uses no additional realization coefficient
or affine-cohomology realization hypothesis.

## Where the brief, the DAG or earlier work was wrong

No existing statement is disputed. The old plan combined a nontrivial raw scalar
restriction square with the formal module/sheafification construction. The
normalization theorem supplies the evaluation and class squares, but does not
itself state compatibility with local scalar multiplication through coherent
restriction. The new node isolates that remaining square while the construction
and sheafification steps are implemented in Lean.

The existing quasi-coherent comparison and module pullback adjunction are used
as tools to prove the functor and additive laws, rather than replacing any step
of the proper-base-change unit route.

## New nodes

`lem-weil-pbc-coherent-raw-scalar-restriction`, implemented by
`AlgebraicGeometry.Scheme.Modules.coherentRawScalarRestriction` in module
`Sheaf.AlgebraicGeometry.CoherentRawScalarRestriction`, isolates
scalar compatibility on raw cohomology. Its docstring and node give the argument
using normalization, coefficient naturality, the tensor-composition restriction
formula and the cartesian projection identity. Its source is the presheaf of
Tag 03Q8 together with the quasi-coherent pullback comparison in Descent,
Tag 03DR. The parent node now records the explicit construction and this single
remaining step. No change record is needed because no existing statement or
definition is changed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
