## What changed

Proved AlgebraicGeometry.ProEtale.directImageComparison with its original statement, including the exactness, unbounded isomorphism, inverse-image coherence, specified derived mate equations, derived direct-image identity/composition, and intrinsic classicality clauses. The three extracted auxiliary theorems are all proved: inverseImageComparisonCoherence, directImageMateCompatibility, and classicalDirectImagePreservation.

The classicality proof constructs the additive exact restriction equivalence from intrinsic constant-ring modules to fixed-scalar sheaves. It constructs the sectionwise direct-image comparison and derives it using the existing exact/K-injective APIs. A canonical homology comparison reconciles the standard and smaller localization models; cohomology and continuity-map naturality identify the classicality predicates. The fixed-scalar assertion follows from boundedBelowComparison, classicalDerivedEquivalence, and the existing acyclic direct-image comparison. The proof then transports back to the recorded intrinsic derived direct image. All constructions are actual functors or isomorphisms, without postponed data.

Adapted the newly landed SupportComparisonPullbackCoherence by explicitly specializing the generalized conjunction at finite rings, with its statement and visibility unchanged.

Generalized ComparisonPullbackCoherence and ComparisonDirectImage by removing unused finiteness assumptions; the latter's composition theorem also loses unused qcqs assumptions on its arrows. Their existing proofs remain unchanged. Moved the identical real definition directImageComparisonPullbackPlusIso into the mate-compatibility module and publicly reexported it from the assigned module. Its name, type and construction remain identical.

## Proved and sorry left

Closed the one original hole, AlgebraicGeometry.ProEtale.directImageComparison. Also proved all three auxiliaries introduced by this delivery:

- AlgebraicGeometry.ProEtale.inverseImageComparisonCoherence (lem-pe-inverse-image-comparison-coherence).
- AlgebraicGeometry.ProEtale.directImageMateCompatibility (lem-pe-direct-image-mate-compatibility).
- AlgebraicGeometry.ProEtale.classicalDirectImagePreservation (lem-pe-classical-direct-image-preservation).

Original holes closed: 1 of 1. Holes added: 0. Holes remaining in delivered modules: 0. No axiom or hollow definition was introduced. Existing declared dependencies remain dependencies in the intended stage-3 sense. The necessary support-module proof adaptation also compiles with zero holes.

## No longer needed

Removed proof-only imports Mathlib.CategoryTheory.Sites.ConstantSheaf, WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence, Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets, Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison, Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence, Sheaf.AlgebraicGeometry.ProEtaleInverseImage, Sheaf.AlgebraicGeometry.ProEtaleSiteComparison, Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence, Sheaf.CategoryTheory.RingedSiteModules, Sheaf.CategoryTheory.SitePullbackAbelianExact, Sheaf.SixFunctors.ClassicalDefinition, WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs. The bounded-below comparison and classical-derived-equivalence imports are used in the proved classicality module. Removed Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport: its transport interface assumes finite coefficients and cannot supply the arbitrary-ring classicality step. No additional library module is asserted globally unreachable. The separate full-faithfulness/Yoneda argument of step 4 is unnecessary for invertibility, since the existing acyclicity proof establishes the canonical map directly. The unit's direct-image comparison and classical-derived-equivalence route remains the route of the three extracted obligations.

The inverse-image coherence module removed its redundant imports of ProEtaleConstantDerivedDirectImage, ProEtaleDerivedCategory, ProEtaleConstantRingOperations, WeilConjectures.AlgebraicGeometry.DerivedCategories, ComparisonDirectImageCanonicalMate, ComparisonDirectImage, ClassicalContinuityMap, WeilConjectures.SixFunctors.ProEtale.Comparison, RightDerivedFunctor.PlusBaseChange, RightDerivedFunctor.PlusComp, and Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus. It now imports only ComparisonPullbackCoherence and Comparison.LowerStarAcyclic; all eleven other inherited public imports were redundant for its statement and proof. The assigned module retains its existing public imports. The new classicality module does not import ComparisonDirectImage: it uses the existing arbitrary-coefficient acyclic comparison directly.

The former direct proof dependencies lem-weil-pbc-conjugate-iso-unit-equation, lem-weil-pbc-site-pullback-abelian-exact and lem-weil-pbc-exact-functor-derived-factorization are unnecessary as separate proof obligations here: existing exactness instances and the existing exact-localization APIs provide their required consequences. The separate sbc-def-base-change-map interface and lem-weil-pbc-mate-pasting are also unnecessary for this proof: the existing derived adjunctions, the normalized mate equations, and ComparisonDirectImage's already proved identity/composition theorems give the specified equations directly. This removes those direct DAG proof edges; it does not assert that their modules are globally unreachable from other targets. Definition dependencies remain available through the statement imports.

## Where the brief, the DAG or earlier work was wrong

ComparisonDirectImage and ComparisonPullbackCoherence imposed unused Finite hypotheses despite having generic proofs. The direct-image composition proof also used no qcqs assumptions on its component arrows. Removing those assumptions exposes the already proved general statements.

The finite-only SfIntrinsicRealizationTransport cannot provide the arbitrary-ring transport required by classicality. The present proof constructs the needed restriction equivalence privately, using the constant-section unit and module sheafification. ClassicalDerivedDefinitions explicitly uses standard-localization homology while other APIs use smaller Hom universes. The canonical fixedHomologyStandardIso and a local standard-localization instance handle that difference without changing any public definition or target.

On resumption, replaced the stale sandbox copy of lem-weil-pbc-comparison-pullback with the current node, preserving its support-prefixed specialization, proof and newer independent review. Added only the underlying generalized comparison_pullback_coherent to its declaration list and explanatory note. The generalized unprefixed comparison_pullback_coherent remains the underlying proved API used by the new inverse-image coherence theorem.

Current-source consumer checks on 2026-10-19 found no additional textual caller of any changed declaration. Refreshed the change-record tables with new transitive importers; historical rows are retained. The assigned theorem statement was compared textually with the current source and is identical.

The inherited split is completely discharged. Empty schemes, the zero ring and arbitrary cohomological lower bounds are allowed throughout: the constructions use only the sheafification unit, equivalence APIs, adjunction identities and the supplied lower bound.

## New nodes

lem-pe-inverse-image-comparison-coherence records the two inverse-image equations and is proved by cancelling the inverse comparison in the existing coherence theorem.

lem-pe-direct-image-mate-compatibility records the specified derived unit/counit equations and is proved by normalization of the underived mate, exact localization, right-derived uniqueness, and Mathlib's mate equations. It owns the unchanged real pullback comparison definition.

lem-pe-classical-direct-image-preservation records preservation of intrinsic classicality and is proved by the explicit scalar-restriction, derived-transport and classical-derived-equivalence argument above. None of the three nodes leaves a sorry.

Change records: coord/changes/J3-ComparisonDirectImage-arbitrary-coefficients.md, coord/changes/J3-ComparisonPullbackCoherence-arbitrary-coefficients.md, coord/changes/J3-pullback-comparison-definition-location.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence is unclaimed at this check. Its original proof at line 274, `exact comparison_pullback_coherent`, fails against the generalized dependency:

```text
Type mismatch: comparison_pullback_coherent has type
  ComparisonPullbackCoherent (Type (u + 1)) ∧
    ComparisonPullbackCoherent AddCommGrpCat ∧
      ∀ (Λ : Type (u + 1)) [Ring Λ], ComparisonPullbackCoherent (ModuleCat Λ)
but is expected to have type
  supportSiteComparisonPullbackCoherent (Type (u + 1)) ∧
    supportSiteComparisonPullbackCoherent AddCommGrpCat ∧
      ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ],
        supportSiteComparisonPullbackCoherent (ModuleCat Λ)
```

Refreshed the sandbox consumer from the current source on final resumption, retaining its current imports. Changed only that proof line into the same three conjuncts, explicitly binding the retained Finite instance in the third. The original declaration signature, visibility, docstring and imports remain identical. No other support-module line changes.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
