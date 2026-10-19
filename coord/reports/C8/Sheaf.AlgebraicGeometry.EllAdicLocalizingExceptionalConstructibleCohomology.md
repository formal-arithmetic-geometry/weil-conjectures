## What changed

Completed the original cohomology theorem without changing its signature. The proof
establishes noetherianity, identifies general bounded constructibility with finite
constant-model bounded constructibility and their fixed u+1 localizing hulls, and
transports the supplied adjunction through full inclusions. A real case split on the
coefficient certificate combines the rational and integral geometric results.

The four retained new modules are all proved. The coefficient-heart comparison uses
finite-free covers in the rational cases. In the integral case an explicit isometric
valuation-ring equivalence, including ULift and equality of spectral and embedded norms,
identifies the actual condensed rings. Restriction of scalars transports finite
presentations, covering pullbacks and strata. The reverse heart comparison maps finite
scalar presentations through the additive left adjoint upperStarFromPoint.

Completed both geometric components. For rational coefficients, the field's finite
image in PadicAlgCl supplies the continuous condensed ring isomorphism; Qbar retains
its finite-subextension-valued ring. The finite-Tor comparison and localizing principle
identify the small-index hull with the gluing theorem's hull. The identity compactification
of the proper map gives an explicit isomorphism from its actual compact-support functor
to ambient Rg_*. Adjunction.restrictFullyFaithful transports the supplied adjunction;
rationalRestrictionGlue then gives bounded constructibility and hence every cohomology.

For integral coefficients, integralRestrictionGlue first treats a finite intermediate
field on the same proper compactification. For an arbitrary embedded finite extension,
construct the isometric equivalence of its valuation ring with that of its fieldRange,
and the resulting condensed ring isomorphism. Derived coefficient-comap equivalences
preserve the fixed-size hulls. derivedComapLowerStarIso compares the actual pushforwards,
and restrictFullyFaithful transports the supplied adjunction. The equivalence counits
and the homology-comap isomorphism transport the image-field conclusion back to G(K).
All coefficient, hull, adjunction and homology transports are proved in Lean.

Only the item, its route node, four new proved modules and their nodes are delivered.
No existing definition or signature changes, and no consumer adaptation is required.
All five modules had compiled together through lcompile.py in the retained work; the
final delivery dry run repeats compilation and the declaration-axiom probes after pruning.
No compilation limit was raised. Empty schemes, zero ranks and integral torsion remain
covered; no nonempty or free-module hypothesis is added.

The interface-context classification is documented in
`coord/changes/ell-adic-localizing-interface-context.md`.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible.
Its exact original statement is proved from existing declared dependencies and the
following new, completely proved statements:

- AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_constructible_constantModel
  and ellAdic_constructible_iff_constantModel;
- AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_integral_constructible_constantModel;
- AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_rational_constantModel_rightAdjoint_homology_constructible;
- AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_integral_constantModel_rightAdjoint_homology_constructible.

Zero sorry remains in any of the five delivered modules, and zero holes are added.
Relative to the earlier report, all three former split-off holes are now proved.
Relative to repository sources, the net local change is one hole closed and none added.
This is a proof from existing project lemmas, some of which still contain sorry,
including the geometric gluing/localizing inputs; it does not claim those inputs are
axiom-free. No sorry is hidden in a definition, private helper or partial proof.

## No longer needed


Removed these proof imports from the original item module (relative to current sources):

- Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
- Sheaf.Paper.CondensedQbarLfpLocalTriviality
- Sheaf.Paper.IntegralLfpLocalTorsionCharts
- Sheaf.Paper.IntegralLfpLocallyFreeResolution
- Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure
- Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
- WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
- Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
- Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
- Sheaf.Paper.CondensedConstantConstructibility
- Sheaf.Paper.IntegralLfpConstantModelComparison
- Sheaf.Paper.LocalizingAdmissibleCoefficients
- Sheaf.Paper.LocalizingClosureCtfEqualsBc
- Sheaf.Paper.LocalizingExceptionalAdjoint
- Sheaf.Paper.ProperExceptionalRestriction
- Sheaf.Paper.RationalExceptionalRestriction
- Sheaf.SixFunctors.IntegralBrownAdjoint
- Sheaf.SixFunctors.IntegralExceptionalRestriction

The comparison module additionally drops Sheaf.AlgebraicGeometry.FiniteConstantLocalModel;
its reverse implication now uses the defining finite presentations directly.

The main proof no longer directly uses these original planned proof dependencies:
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
def-weil-pbc-internal-abelian-sheaf-module-equivalence,
lem-weil-pbc-condensed-lfp-local-triviality,
lem-weil-pbc-condensed-qbar-lfp-local-triviality,
det-def-sfb-constructible-local-model,
lem-sfb-integral-lfp-constant-model-comparison,
det-def-localizing-closure-ctf-equals-bc,
sk-prop-sf-existence, det-cor-existence-ii-restriction,
sk-thm-restriction, det-prop-int-brown-adjoint, sk-thm-int-restriction,
det-sp-unique-right-adjoint, and def-sfb-constructible-module.
Coefficient comparisons and geometric arguments remain in their component nodes where
needed; these are not claims that all those modules leave the targets' global closure.
No entire existing module is claimed globally unnecessary. The obsolete tool approvals for lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
def-weil-pbc-internal-abelian-sheaf-module-equivalence and
det-def-sfb-constructible-local-model are removed in their original order. The remaining
approvals are retained because the geometric components keep the prescribed source route. The rational
component uses det-thm-restriction-glue rather than directly applying sk-thm-restriction,
lem-weil-pbc-condensed-qbar-lfp-local-triviality or det-sp-unique-right-adjoint. The integral
component uses det-thm-int-restriction-glue rather than directly applying
det-prop-int-brown-adjoint, sk-thm-int-restriction or det-sp-unique-right-adjoint.
The gluing statements retain the prescribed local geometric restriction route.

Removed two redundant proof imports from the retained new rational module:
Sheaf.Paper.ConstantModelTorAmplitude (already exported by LocalizingClosureCtfEqualsBc)
and Mathlib.CategoryTheory.Adjunction.Restrict (exported by DerivedCategory.Adjunction).

## Where the brief, the DAG or earlier work was wrong

The retained report was stale: it said the geometric components still had two holes,
but their Lean proofs were already present and compiled. Both node proof plans now
record the actual completed argument and its direct dependencies.

ProperExceptionalRestriction and RationalExceptionalRestriction expose a larger hull
universe and an all-continuous Qbar coefficient certificate. The exact interfaces needed
here are instead available in RationalRestrictionGlue and IntegralRestrictionGlue.
The hull comparison proves equality with the fixed u+1 convention, rather than changing
that convention. The rational gluing theorem accepts the finite-subextension-valued
padicAlgClRingObj directly. The integral gluing theorem's finite-intermediate-field
restriction is handled by the explicit coefficient and derived-hull equivalences.
These are resolved interface differences, not remaining obligations.

The source library's bounded proper-adjoint interface would introduce an import cycle,
so this proof uses the supplied unbounded hull adjunction throughout. The unit
sk-cor-existence-ii has empty realized statement/step lists; the prescribed proper,
rational and integral restriction route is retained. The original target and all
existing statements keep their meanings. The retained interface-context change record
documents the conservative preflight classification; it records no mathematical
interface change.

## New nodes

lem-sfb-adic-constructible-constant-comparison: the proved coefficient-heart comparison
and iff companion. Field and Qbar cases use the existing local-free-cover inputs;
the integral case uses the proved integral comparison. The reverse implication is
proved directly from the defining finite presentations.

lem-sfb-adic-integral-constructible-constant-comparison: the proved integral heart
comparison, using an explicit valuation-ring isomorphism, spectral norm equality,
universe lift, and transport of finite presentations and finite constant local models.

lem-sfb-adic-rational-constant-model-cohomology: the proved rational geometric case,
using finite-field image normalization, the fixed-size hull equality, proper identity
compactification, supplied-adjunction restriction and rationalRestrictionGlue.

lem-sfb-adic-integral-constant-model-cohomology: the proved integral geometric case,
using integralRestrictionGlue on image finite fields and explicit transport through
coefficient-derived hull equivalences for arbitrary embedded finite extensions.

Each new node retains its recorded source and actual search history. None leaves an
unproved intermediate theorem for another session.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
