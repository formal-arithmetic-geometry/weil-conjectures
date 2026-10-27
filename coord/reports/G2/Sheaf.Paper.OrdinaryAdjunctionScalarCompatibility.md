## What changed

Proved the completion-unit Hom bijection, its integral linearity, the coefficient-adjunct
normalization, the integral scalar equations, their rationalizations, strict scalar tower
coherence, coefficient-model rational Hom coordinates, and the common-stage equality
criterion. The proofs use the existing intrinsic completion reflector, specified mate
maps, and balanced tensor universal properties. All existing declaration signatures,
definitions, docstrings and public imports are preserved. Added proved private helpers
and private imports of Mathlib.CategoryTheory.Limits.HasLimits, PbcScalarExtension and
FdIntegralIdentityRationalEquivalence (the latter two with `import all` for their proved
scalar-action helpers). Updated the node's proof route and proof dependencies.

Validation: the complete module compiled through lcompile.py (59.1 seconds); the only
warning was an unused section variable, now suppressed locally while preserving its signature.
The delivery command reruns the final compile and preflight.

## Proved and sorry left

Original holes: 14. Closed: 10. Added: 0. This is proof progress, with no decomposition.

- `WeilConjectures.purOrdinaryHom_bijective` is proved.
- `WeilConjectures.purOrdinaryHom_linear` is proved.
- `WeilConjectures.purScalarDirectImage_coefficientAdjunct` is proved.
- `WeilConjectures.purRationalHom_existsUnique` is proved.
- `WeilConjectures.purRationalScalarMaps_existsUnique` is proved.
- `WeilConjectures.purOrdinaryAdjunctionScalarCompatibility` is proved.
- `WeilConjectures.purRationalAdjunctionScalarCompatibility` is proved.
- `WeilConjectures.purOrdinaryAdjunctionScalar_tower` is proved.
- `WeilConjectures.purRationalModelHom_existsUnique` is proved.
- `WeilConjectures.purOrdinaryAdjunction_commonStage` is proved.

The four retained original holes are:

- `WeilConjectures.purScalarRightDerivedComparison_normalization`.
- `WeilConjectures.purOrdinaryAdjunctionScalar_identity`.
- `WeilConjectures.purOrdinaryAdjunctionScalar_bounded`.
- `WeilConjectures.purScalarModel_coherence`.

Every retained hole belongs to `lem-pur-ordinary-adjunction-scalar-compatibility` and
retains its original source and proof docstring. No holes occur in private helpers or
definitions. No new theorem holes, modules, axioms, or statement changes were added.

## No longer needed

Removed these private proof imports, since the completed proofs do not use them:

- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.SfIntegralDirectImageConstructible`.
- `Sheaf.Paper.SfDerivedDirectImage`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.

The proof route no longer needs these node dependencies:

- `def-weil-pbc-projection-formula-arrows`: the existing actual scalar mate definition
  supplies the map directly, so no projection-arrow construction is needed here.
- `lem-pur-ringed-coefficient-restriction-counit`: iterated mate calculus proves the
  coefficient-adjunct equation directly from the actual mate definition.
- `lem-sp-completed-pullback-adjunction`: the intrinsic completed-ring reflector already
  gives the needed Hom bijection.
- `lem-weil-finite-free-completed-scalar-comparison` and
  `lem-weil-pbc-constant-completion-equivalence`: the completed-ring reflector and the
  published scalar/completed-pull unit equation provide the specified normalization.
- `lem-weil-pbc-mate-pasting`: the tower clauses are the published scalar coefficient
  equations conjugated by the strict comparison.

No module is withdrawn. Public imports remain available to consumers. The node retains
the dependencies of its four unfinished arguments; removing an unused private import is
not a claim that those remaining dependencies are globally prunable.

## Where the brief, the DAG or earlier work was wrong

The original route expanded several K-injective and constant-coefficient calculations
that are unnecessary once the actual completed-ring adjunction and scalar maps are used.
The statements themselves are unchanged. The common-stage statement is precisely an
existential equality criterion for the explicitly defined rational scalar maps, so its
proof only needs their compatibility and the injectivity of the stage adjunction.
The coefficient-model Hom proof reuses the existing proved scalar-action and localized
coefficient-ring calculations rather than introducing another localization comparison.
The right-derived normalization, identity coherence, bounded constructibility and
coefficient-model coherence remain original obligations, not newly split-off lemmas.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
