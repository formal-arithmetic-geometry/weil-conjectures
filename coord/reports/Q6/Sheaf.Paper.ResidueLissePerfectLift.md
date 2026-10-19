## What changed

Replaced the proofs of `AlgebraicGeometry.Scheme.residueLisseConstant_additive`,
`residueLisseConstant_preservesFiniteLimits`, and
`residueLisseConstant_preservesFiniteColimits` in
`lean/Sheaf/Paper/ResidueLissePerfectLift.lean`. Additivity is checked after the faithful
underlying abelian-sheaf functor; finite-limit preservation follows from the usual
constant abelian-sheaf functor and reflection of limits. Finite-colimit preservation
is proved pointwise for constant module presheaves and then composed with module
sheafification. Every declaration signature and all definitions are unchanged. The dependency imports
added to the current shared source are retained. The resumed sandbox compiled
through `lcompile.py` in 5.3 seconds with exit code 0.

## Proved and sorry left

Closed three of the five original holes, with no holes added. All five declarations
are attached to `lem-weil-pbc-residue-lisse-perfect-lift`. Closed:
- `AlgebraicGeometry.Scheme.residueLisseConstant_additive`.
- `AlgebraicGeometry.Scheme.residueLisseConstant_preservesFiniteLimits`.
- `AlgebraicGeometry.Scheme.residueLisseConstant_preservesFiniteColimits`.

Remaining original holes, both attached to
`lem-weil-pbc-residue-lisse-perfect-lift`:
- `AlgebraicGeometry.Scheme.residueLisseConstantComparison_exists`.
- `AlgebraicGeometry.Scheme.residue_lisse_perfect_lift`.

This is a partial proof delivery, not a decomposition. No new modules or obligations
are introduced. The main theorem retains its complete original six-step proof plan.

## No longer needed

None. The main lifting proof remains open, so its recorded proof dependencies and
imports have been retained. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned file was briefly absent during the initial shared-checkout refresh,
then became available without any worker modification. The first remote compile
received no server answer; a later retry returned ordinary compiler feedback.
The attempted proof of `residueLisseConstantComparison_exists` constructs the map
by commutative-ring sheafification and proves local bijectivity, but its final
normalization equations still required coercion glue between the commutative-ring
and ring presentations. That unfinished attempt is not included in the delivery.
No mathematical statement defect was found. The existing constant-module APIs
suffice for the three exact-functor infrastructure lemmas; no new dependency or
statement repair was necessary.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
