## What changed

In Sheaf.Paper.IntegralCriterionReductions, filled five of the eight original theorem
holes, with no change to any original public signature or definition.

The normalized abelian comparison now follows from sfb_integral_coefficient_limit.
A proved private helper shows that every natural endomorphism of finite constant set
sheaves is the identity: terminality fixes the singleton component, naturality fixes
all labels, and the sheafification universal property fixes all sections. This makes
the finite representation independent of the witness. The prescribed quotient equations
then remove the auxiliary limit-cone choices.

The additive endpoint identification follows from equality of the two coefficient
topologies. Equality of their distance functions gives equality of their pseudometric
structures and hence their induced integer topologies. Congruence for the continuous
ring-sheaf construction and the point pullback gives the first endpoint equality;
the completed endpoint equality is definitional.

The section-action functor is additive by the existing section-module equivalence.
Restriction along a ring isomorphism is explicitly an equivalence: the two round trips
use the identity on sections, with scalar actions identified by the inverse equations.
The two final corollaries combine the original main statements by propositional reasoning.

Added proof-only imports of ConstantSheafOver and Limits.Types.Products. The unit-route import of IntrinsicFiniteTorsionConstructibility is retained.
A file-local irreducibility setting for upperStarFromPoint prevents the endpoint
congruence from unfolding the entire inverse-image construction. It changes no
statement, definition body or exported attribute. The required change record is
coord/changes/T3-integral-criterion-local-opacity.md.

Validation: the complete delivery module compiled without errors or warnings through
lcompile.py in 4.0 seconds after removing unused proof imports. The delivery tool performs
the final compile and preflight. No axiom, new sorry, new module, or arbitrary witness
definition is introduced. The two corollaries still depend on the original main holes;
the hole count describes closures, not completion of the whole criterion.

## Proved and sorry left

Closed five original holes:

- AlgebraicGeometry.ProEtale.integralLimitAbComparison_existsUnique
- AlgebraicGeometry.ProEtale.integralSectionAbIdentifications
- AlgebraicGeometry.ProEtale.integralSectionFunctor_properties
- AlgebraicGeometry.ProEtale.continuousIntegralConstructible_iff_first_reduction
- AlgebraicGeometry.ProEtale.sfIntegralConstructible_iff_first_reduction

Three original holes remain unchanged, all attached to
`det-prop-integral-criterion-reductions`:

- AlgebraicGeometry.ProEtale.integralSectionRingIso_existsUnique
- AlgebraicGeometry.ProEtale.continuousIntegralConstructible_iff_sfIntegralConstructible
- AlgebraicGeometry.ProEtale.integral_reductions_constructible_iff

Holes closed: 5. Holes added: 0. Split off: 0. Remaining: 3 of the initial 8.
The attempted ring reconstruction is omitted because its required instance and transport
identifications did not compile; its original named theorem and proof plan remain intact.

## No longer needed

Removed these unused proof-only imports from this partial implementation:

- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Mathlib.Topology.Algebra.Valued.LocallyCompact
- Sheaf.AlgebraicGeometry.ProEtalePointPullback
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Mathlib.Algebra.Homology.DerivedCategory.ShortExact
- Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
- Sheaf.Paper.DerivedCompleteOnSlices
- Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
- Sheaf.AlgebraicGeometry.IntegralConstantCompletion

No mathematical node or module is claimed to be pruned: the unfinished main induction
and presentation comparison still need their original DAG route. The public imports
are unchanged. The point-pullback definitions are already supplied by the public
coefficient-comparison imports. The DAG remains unchanged because its original main
proof plan is retained; this packet fills auxiliary proofs and logical corollaries.

## Where the brief, the DAG or earlier work was wrong

The current proof dependencies expose several coefficient presentations. The successive
quotient triangle is stated for principal-power quotient sheaves and supplied cochain
models, whereas this item uses continuous internal finite coefficient sheaves. Connecting
these requires explicit coefficient isomorphisms and normalized derived comparisons;
the triangle cannot be applied directly merely from the reduction objects.

The integral completion presentation accepts a supplied Encoding but its existence theorem
returns an existential Encoding. Identifying it with this item's specified ring comparison
requires a normalization argument. Its completeness conclusion is forward only, whereas
the predicate equivalence in this module needs both implications. These are outstanding
glue requirements, not counterexamples to any stated theorem.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
