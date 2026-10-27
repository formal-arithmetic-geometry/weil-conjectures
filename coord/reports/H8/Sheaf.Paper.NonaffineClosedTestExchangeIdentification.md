## What changed

Proved the original nonaffine_test_naturality from two strictly smaller naturality
calculations: section comparison for one arbitrary scheme map and a pro-etale test,
and closed-unit comparison for a map of lifted tests. Structural maps are made weakly
etale explicitly. The first calculation is applied separately to f and fZ; the second
is evaluated at the underlying unbounded object K.obj. Every original signature and
public import is retained. Two new modules contain the source calculations.

The larger identification construction was explored but did not pass elaboration
within the fixed limit; it is not claimed as proved in this delivery. No timeout limit,
definition, instance or target statement was changed in the delivered files.

## Proved and sorry left

Closed one of three original holes by decomposition:
AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.nonaffine_test_naturality.

Two original holes remain, both on node
lem-sfb-nonaffine-closed-test-exchange-identification:

- AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.actual_ambient_exchange.
- AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.nonaffine_closed_test_exchange_identification.

Two new holes are added:

- AlgebraicGeometry.ProEtale.ClosedTestSectionSteps.proetale_section_localization
  in Sheaf.Paper.ClosedTestSectionLocalization,
  node lem-sfb-nonaffine-proetale-section-localization.
- AlgebraicGeometry.ProEtale.ClosedTestSectionSteps.closed_derived_evaluation
  in Sheaf.Paper.ClosedTestClosedEvaluation,
  node lem-sfb-nonaffine-closed-derived-evaluation.

This is a decomposition, not a net hole reduction: one upper hole closed, two lower
holes added. Each new statement is one part of the original three-conjunct statement;
neither repackages the original hypotheses and conclusion. The section calculation
has only one arbitrary source morphism; the closed-unit calculation has no X or f.

## No longer needed

No original module or node is withdrawn or claimed globally unnecessary. The original
proof plan and dependencies remain for the two original open declarations.
The following direct proof imports are removed because the completed naturality proof
uses the two new source calculations; they may still be needed to prove the other
original holes and are retained in their DAG plan:

- Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs.
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs.
- Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology.
- WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible.
- WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine.
- Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit.
- Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison.
- Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp.
- Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization.
- Sheaf.Paper.LocalizeRingedSiteMorphismGeneral.
- Mathlib.CategoryTheory.Functor.Derived.Adjunction.
- WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions.
- Sheaf.Paper.RingedDerivedSliceLocalization.
- Mathlib.Algebra.Homology.DerivedCategory.KInjective.

The abandoned draft unnormalized square and its new node are not delivered because
no delivered proof uses them. The new statements assert only naturality; the draft
isomorphism and shift conclusions were pruned as unnecessary to this partial proof.

## Where the brief, the DAG or earlier work was wrong

The source plan's naturality step needs two separate bridge statements to the exact
internal-module maps in this item. Existing affine-source naturality has an IsAffine X
hypothesis and cannot prove the source-general result. The specified ringed-site
interfaces do not directly give these normalized comparison naturality equations.
An affine-pro-etale object's structure map does not synthesize WeaklyEtale automatically;
proAffineEtale_le_weaklyEtale applied to its prop field supplies it.
The original unit route is retained, and the two remaining original proofs are open.

## New nodes

lem-sfb-nonaffine-proetale-section-localization: test restriction naturality for the
canonical section comparison, source steps 2,4,5,9, in
lean/Sheaf/Paper/ClosedTestSectionLocalization.lean. Zero complexes, identity arrows
and empty tests use the same presheaf restriction identities.

lem-sfb-nonaffine-closed-derived-evaluation: closed-unit comparison naturality in a
lifted test arrow, source step 9, in lean/Sheaf/Paper/ClosedTestClosedEvaluation.lean.
It requires no source scheme or exchange map. For I=0 it is the identity closed
restriction; for I=A the same equality holds over empty closed tests.
No change record is needed because no existing interface or definition is changed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
