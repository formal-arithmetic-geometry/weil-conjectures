## What changed

The original statement and canonical section isomorphism are unchanged. The proof lifts
h from the base and uses naturality of the specified section isomorphism to cancel its
normalization. Three new modules provide ordinary etale affine-line fullness, the finite
lisse coefficient bridge, and the endomorphism lift. All work is in the assigned sandbox.
No definitions or existing signatures change and no consumer adaptations are needed.

The ordinary etale calculation uses the existing source theorem
Etale.isIso_upperStarSectionsMap, recorded by
lem-sbc-module-chart-sections-flat-connected. The projection is smooth and affine with geometrically
irreducible fibres, so its unit is an isomorphism on every etale object. This replaces the
long set-section retraction calculation by an existing module-section API. Comparison
fullness and coefficient-realization units then transport the lift. The unit route of
sk-thm-dnc and the parent arbitrary-base uniqueness assertion are preserved.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.proEtale_a1_pullback_endomorphism_rigidity (the item's
one original hole). Added holes: none. The new declarations are
AlgebraicGeometry.etale_a1_pullback_full,
AlgebraicGeometry.Scheme.proEtale_intrinsic_lisse_fixed, and
AlgebraicGeometry.Scheme.proEtale_a1_pullback_lift.

Validation: all four files compile through lcompile.py --all with no errors or warnings
(0.7, 1.4, 3.8 and 3.8 seconds in the successful verification). The required delivery
checks also compile and probe the declarations. Empty bases, zero rings/modules, disconnected and nonreduced bases need
no extra hypotheses: affine-space geometric irreducibility is valid over every field,
and the coefficient arguments use covers and colimits, not conservativity of arbitrary
pro-etale geometric stalks.

## No longer needed

Removed direct proof imports from the item:
Sheaf.AlgebraicGeometry.ProEtaleInverseImage;
Sheaf.CategoryTheory.ConstantLeftModuleInverseImage;
Sheaf.AlgebraicGeometry.ProEtaleSiteComparison;
Sheaf.Paper.ProEtaleLisseOrigin;
Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel;
Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence;
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs;
Mathlib.CategoryTheory.Limits.MorphismProperty;
WeilConjectures.AlgebraicGeometry.EtaleConnectedFibresSectionCompatible;
WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits;
WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction;
Mathlib.Algebra.MvPolynomial.Basic;
Mathlib.RingTheory.Spectrum.Prime.Topology.

The removed direct dependencies lem-pe-constant-left-module-inverse-image and
def-weil-proetale-inverse-image are supplied through the existing canonical intrinsic
realization and pullback API. The explicit
lem-weil-pbc-etale-base-change-finite-limits dependency is supplied by the existing
Mathlib base-change instances, rather than a separate proof import.

The separate set-valued section theorem
lem-weil-pbc-etale-sections-flat-qc-connected-fibres is replaced by the existing
module-valued chart-section theorem lem-sbc-module-chart-sections-flat-connected.
The coefficient bridge compares additive colimits directly and does not use
lem-weil-proetale-constant-sheaf-stalk as a proof dependency.

The lift still needs ordinary comparison fullness and its pullback comparison, accessed
through their source declarations; etale origin remains necessary. The separate polynomial
domain and prime-closure nodes lem-weil-pbc-polynomial-ring-domain and
lem-weil-pbc-spec-irreducible-closed-subsets-primes are replaced by Mathlib's existing
AffineSpace geometric irreducibility instance. The explicit set-section restriction and
composition nodes lem-weil-pbc-sets-etale-inverse-image-restriction and
lem-weil-pbc-sets-etale-inverse-image-composition-units and the direct compatibility node
lem-weil-pbc-etale-connected-fibres-section-compatible are no longer applied directly:
the existing module section-isomorphism theorem packages that calculation. Their source
modules may remain transitively needed by that theorem. There is no claim that those
transitive dependencies leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt had two elaboration errors: the coefficient bridge tried to
synthesize an IsIso instance before passing to the underlying additive map, and the
functor comparison omitted the left unitor before inserting the realization unit. Both
are repaired without changing statements.

The lisse-origin declaration now uses fixed-module coefficients, while the item uses
intrinsic constant-ring modules. The coefficient equivalence alone does not immediately
provide local-constancy and finite-stalk transport. The bridge makes that step explicit.
Its local-constancy and stalk-colimit arguments reuse the private arguments of
ProEtaleConstantModuleConstructibility without changing that module's interface.

## New nodes

new-lem-pur-etale-a1-pullback-full records the objectwise etale unit calculation.
new-lem-pur-intrinsic-lisse-fixed records the coefficient bridge, with actual
sheafification-unit and colimit comparisons.
new-lem-pur-a1-pullback-lift records lifting through the full comparison composite.
No change record is needed: all existing public statements, definitions and public
imports remain unchanged; the new statements are in new modules.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
