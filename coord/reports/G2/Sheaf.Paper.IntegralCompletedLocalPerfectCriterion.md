## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.integralCompletedLocalPerfectCriterion`
by a Lean assembly of the uniform reduction criterion, finite-field stratification,
perfect-strata uniform reductions, and finite-stratum detection of the intrinsic
completion unit. Its signature is unchanged.

The proof includes an explicit comparison between `integralConstantDerived` and
the derived scalar-extension model required by `perfect_strata_uniform_reductions`.
It compares the scalar maps by the finite limit projections, uses uniqueness of
scalar adjunctions, and applies the K-flat extension counit to a bounded projective
representative. It then refines covering sieves by covering presieves and transports
the resulting cohomology bounds and constructibility through exact scalar restriction.

In the forward direction it extracts an actual bounded constructible etale origin
of the residue reduction from normalized local effectivity. It proves maximality
of the lifted uniformizer ideal, applies finite-field stratification, transports
the residue chart isomorphisms across the chosen origin, and lifts on each fixed
stratum. In the reverse direction it detects completeness on the supplied chart
covers and uses the proved uniform criterion to recover both the tower models and
the compatible etale origins.

Two unresolved local coefficient-presentation comparisons are stated in new modules:
`Sheaf.Paper.IntegralPerfectChartComplete` and
`Sheaf.Paper.IntegralResidueStratumLift`. Only the item, these new modules and their
nodes, and the item's proof fields are changed. No shared definition, target,
existing public signature or public import is changed.

Validation: both new statement modules compiled, and the completed item compiled
in 17.1 seconds after removing development options. No profiler, trace option,
or transparency override remains in the delivery. The delivery tool performs the
final combined compile and preflight.

## Proved and sorry left

Original holes closed: 1, in
`AlgebraicGeometry.Scheme.integralCompletedLocalPerfectCriterion`.
The combination proof and every private helper in the item have no sorry.

Holes added: 2, each with proof exactly `by sorry` in its own module:

- `AlgebraicGeometry.Scheme.integralPerfectChart_complete`
  (`lem-weil-pbc-integral-perfect-chart-complete`): completeness for the ordinary
  datum pullback to the underlying scheme of one given perfect chart, for every
  representative and finite generating family.
- `AlgebraicGeometry.Scheme.integralResidueStratum_lift`
  (`lem-weil-pbc-integral-residue-stratum-lift`): lifting already supplied perfect
  residue models on an etale cover of one fixed stratum to integral perfect models.

This is a decomposition: 1 original hole closed and 2 local holes added, net -1
before considering the unchanged dependencies. It is not a claim that the full
criterion is axiom-free. Neither new statement chooses a global stratification,
provides a global cohomological bound, or supplies the compatible etale origins.
The original module has zero holes. The delivery has two holes in total.

Edge cases checked in formulating the new statements: empty schemes and charts,
the zero perfect complex, arbitrary perfect shifts, and torsion perfect complexes
such as the two-term uniformizer-power resolution. No bound on an arbitrary
pro-etale covering scheme is assumed. Coefficient exponent zero is not used:
the reduction index 0 throughout means the positive exponent 1.

## No longer needed

Removed the original unused direct proof imports
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` and
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`. Their declarations remain
available through the existing comparison results where required.

The item no longer directly invokes the following planned dependencies:
`lem-weil-pbc-uniform-local-model-cohomology`,
`lem-weil-pbc-normalized-constructible-local-effectivity`,
`lem-weil-pbc-normalized-etale-origin-witnesses`, and
`lem-weil-pbc-finite-ring-constructible-derived-origin`.
The proved `lem-weil-pbc-uniform-reduction-criterion` provides the tower/origin
assembly and the needed residue presentation. The explicit finite-ring-origin
module is consequently not imported by this proof.

The coefficient-completeness, residue-lifting and perfect-model-completeness
calculations remain needed by the two local nodes. In particular the existing
approved use of `lem-sfb-adic-perfect-model-complete-reduction` is retained.
No existing module is withdrawn and no globally unused module is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and the unit route is retained. The planned argument
suppresses two substantial Lean presentation changes: the residue lifting theorem
uses the unlifted coefficient universe, whereas the item uses `PbcIntegralRing`;
and local ideal completeness is stated on a small site model, whereas the item
uses a slice of the actual inverse-image completed ring. The two new local nodes
record these comparisons explicitly. They do not duplicate the former rejected
uniform-cohomology or normalized-origin generalizations.

The raw scalar-extension model expected by perfect-strata uniform reductions
also differs from the exact-functor realization in the item. That comparison is
fully proved here, including the projective representative and derived counit.

## New nodes

`lem-weil-pbc-integral-perfect-chart-complete` isolates a single chart calculation:
finite projective completed constants are complete, and the slice/site and actual
coefficient comparisons preserve their completion units. This is strictly below
global completeness detection, which is proved in the item. It uses the already
approved perfect-model theorem as a tool; its generic local coefficient calculation
is not a proper-base-change unit step.

`lem-weil-pbc-integral-residue-stratum-lift` isolates residue perfect lifting and
coefficient/universe transport on one specified immersion. The item itself obtains
the residue etale origin, constructs its finite stratification, supplies its local
perfect residue models, and combines the resulting local integral models. The new
node has neither the hypotheses nor the conclusion of the global criterion.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
