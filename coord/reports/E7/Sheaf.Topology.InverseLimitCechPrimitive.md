## What changed

Proved `Profinite.exists_inverseLimit_cech_primitive` in
`Sheaf.Topology.InverseLimitCechPrimitive`, preserving its statement and the existing
public import. Added the proof-only import
`Sheaf.Topology.FiniteCoefficientCechPrimitiveLift`.

For each coefficient level, the proof projects the given continuous cocycle and
forms the subtype of continuous primitives. The declared theorem
`Profinite.finite_coefficient_cech_primitive_lift` constructs a successor primitive
with the prescribed reduction. Dependent natural-number recursion starts with the
given primitive and chooses these successors. Their compatibility constructs an
actual map into the inverse-limit subtype; `continuous_pi` and
`Continuous.subtype_mk` prove its continuity for the specified topology. The
primitive equations are the subtype invariants, and the first-coordinate equation
holds by reduction of the recursion at zero.

The argument follows all four existing DAG proof steps and retains its sole proof
dependency, `lem-sfb-finite-coefficient-cech-primitive-lift`, so no node update is
needed. The unit route is unchanged. No new definition, statement, or module was
introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`Profinite.exists_inverseLimit_cech_primitive`
(node `lem-sfb-inverse-limit-cech-primitive`).

No holes remain in the item module. Added holes: none. Split off: none.
The existing finite-coefficient lifting theorem is used as the declared proof
dependency; its existing hole is untouched.

Validation: the item compiled successfully through `lcompile.py` (4.5 seconds,
exit code 0, no warnings). The recursive construction requires no nonempty tuple
space, so empty spaces are covered; zero groups and `n = 0` (degree one) use the
same argument, with the finite lifting theorem applied in degree `n + 1`.

## No longer needed

None. No imports removed and no declared dependency, node, or module pruned.
The existing public import supplies the tuple spaces and deletion maps in the
statement. The added private import supplies the lifting theorem used in the proof.
Library and Mathlib searches found no theorem replacing this prescribed-reduction
Cech construction; the elementary topology uses existing Mathlib lemmas.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The finite-coefficient theorem uses a positive
degree parameter, while this module uses one less than that degree; applying it
at `n + 1` aligns all tuple domains definitionally. No repair was necessary.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
