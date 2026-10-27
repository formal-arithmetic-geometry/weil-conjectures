## What changed

Completed eleven of the module's twelve original holes. Scalar extension now has its
pointwise universal left derived functor, using exact faithful restriction of scalars,
K-flat tensor acyclicity, and the existing resolving-class derived adjunction. The three
derived tensor comparisons have reflexive source/target identities and are invertible
by the source library's derived monoidal comparison. The modulus-unit theorem follows
from the characteristic calculation and the structural map on global sections.

The canonical tensor arrows now have explicit result types and use their original maps
directly. Three named degree-zero comparison isomorphisms share the existing constructions.
The scheme comparison uses the definitionally equal named composite-square construction.
The change record is coord/changes/J4-etale-chart-comparison-typed-interfaces.md.

This is a partial proof delivery. The original upper coherence theorem is retained with
its original statement and one sorry. Attempts to assemble its scalar, scheme and twist
coherence proofs encountered expensive conversions between concrete derived-category
presentations. Unvalidated experiments are confined to scratchpad and are not delivered.

## Proved and sorry left

Closed 11 original holes, with no holes added:

- CategoryTheory.fixedCoefficientScalarExtension_hasPointwiseLeftDerivedFunctor.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.nuTensor_source.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.nuTensor_target.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.nuTensor_isIso.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.etTensor_source.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.etTensor_target.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.etTensor_isIso.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.proTensor_source.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.proTensor_target.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.proTensor_isIso.
- AlgebraicGeometry.ProEtale.EtaleChartComparison.modulus_isUnit.

One original sorry remains:
AlgebraicGeometry.ProEtale.EtaleChartComparison.etale_chart_comparison_isos
(blueprint: lem-sp-etale-chart-comparison-isos). No new modules or split statements were added.
The complete delivery module compiled in 30.6 seconds, with the original instance
registrations and functor abbreviations. The delivery tool runs the required independent
consumer, node, and preflight checks.

## No longer needed

Removed direct proof imports Sheaf.Paper.ComparisonPullbackExact,
Sheaf.CategoryTheory.ConstantLeftModuleInverseImage,
Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses, and
Sheaf.SixFunctors.RingedDerivedMonoidalComparisons. The completed lower proofs use
concrete source-library tensor constructions and
Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction instead.

Removed public imports Sheaf.AlgebraicGeometry.EtaleTorAmplitude,
Sheaf.AlgebraicGeometry.ProEtaleFiniteModules,
WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf, and
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible.
The statement's bounded-constructible finite-Tor predicate is supplied directly by
WeilConjectures.SixFunctors.Etale.Derived.Coefficients.

No DAG dependency or module is claimed globally pruned: the upper theorem still has its
original unfinished proof, and its planned dependencies and maintainer approvals are
retained. No source-library declaration is removed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The tensor source and target statements are definitional equalities. Their explicit
transports can be removed once these equalities are proved. Named natural degree-zero
comparison isomorphisms avoid repeatedly elaborating their large inferred types.

The original top theorem remains unfinished. The delivery does not count its experimental
proofs or any component proof not retained in the compiling module as completed work.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
