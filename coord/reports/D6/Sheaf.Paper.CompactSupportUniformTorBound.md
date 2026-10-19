## What changed

Proved `AlgebraicGeometry.ProEtale.compactSupport_uniform_tor_bound` without changing its
signature, definitions or hypotheses. The private helpers compare the recorded ringed and
intrinsic functors, prove the etale numerical Tor bound using the existing finite projection
formula and finite truncation lemmas, and transport the finite result to every tower level.
No new public declarations or modules are introduced. Updated the node proof to this route.

Pruned unused imports, including six public imports. The theorem interface is unchanged;
the sole downstream importer is `Sheaf.Paper.SmoothPurityTowerBound`. The public-import change is recorded in
`coord/changes/D6-compact-support-uniform-imports.md`.

Validation (2026-10-19): an ordered server compile of the sandbox theorem and the
unchanged current consumer succeeded: theorem 54.6 s, consumer 29.2 s, exit code 0,
with no warnings. The downstream check finds only `Sheaf.Paper.SmoothPurityTowerBound`
(current holder J3); the new comparison import is acyclic. A text comparison confirms
the theorem signature is identical, and all Lean lines have at most 100 characters.
The required delivery dry run passed, including compilation and the axiom probe;
review class CODEX covers the updated node, local proof attribute and removed public imports.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.compactSupport_uniform_tor_bound`
(node `det-sp-tower-bound-uniform`). Added 0 holes; split off 0 statements.
The delivered Lean module contains zero `sorry`s. Existing imported theorem holes are
used as permitted by stage 3; none is copied or renamed into a new obligation.

## No longer needed

Removed these direct imports (some remain available transitively where another API needs
them; this does not claim their removal from the global targets' closure):

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.Paper.ConstantModelTorAmplitude`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `Sheaf.AlgebraicGeometry.ProperBoundedConstructible`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.Paper.SmoothPurityCoefficientTowers`
- `WeilConjectures.Compactification.NagataCompactification`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.AlgebraicGeometry.Noetherian`

The direct proof no longer needs the following original planned dependency nodes:

- `def-amb-etale-compact-support`
- `def-weil-proper-morphism`
- `det-pe-finite-tor-comparison-noetherian`
- `lem-cbc-extension-zero-base-change`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-kun-0f0g`
- `lem-kun-stalk-as-pullback`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-sf-derived-homology-long-exact`
- `lem-sf-etale-flat-model`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lemma-nagata-open-immersion-qc-over-separated-target`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-comparison-direct-image`
- `prop-weil-pbc-inverse-image-modules-exact`
- `sk-def-sp-coefficient-towers`
- `thm-nagata-compactification`

The source finite-coefficient projection formula supplies the arbitrary test-sheaf identity,
so the local flat-model, K-flat, stalk and signed-totalization argument is unnecessary.
The proved source truncation lemmas supply the interval extension. The supplied
compactification is used directly; a second Nagata construction is unnecessary. The
finite-ring origin and interval APIs replace the larger comparison theorem. The source
bounded-constructible shriek theorem replaces the local open/proper reconstruction.
Positive quotient annihilation is an ideal-membership calculation, so no uniformizer
choice or input-tower boundedness argument is needed for the supplied level comparison.
The unit still follows the finite-coefficient bound and then its levelwise application.

Removed obsolete maintainer-approved tool uses, preserving the order of those retained:

- `det-pe-finite-tor-comparison-noetherian`
- `lem-cbc-extension-zero-base-change`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-kun-0f0g`
- `lem-kun-stalk-as-pullback`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-sf-derived-homology-long-exact`
- `lem-sf-etale-flat-model`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lemma-nagata-open-immersion-qc-over-separated-target`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-comparison-direct-image`
- `prop-weil-pbc-inverse-image-modules-exact`
- `thm-nagata-compactification`

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The seven-step plan duplicated projection,
truncation and constructibility results already proved in the source library. The original
declaration docstring records that source plan; the updated DAG records the proof actually
written. No unit statement or realized step is bypassed. No forced adaptations were needed.

The DAG retains `lem-fin-extension-by-zero` and `lem-fin-proper-bounded-constructible`
as the mathematical open/proper finiteness inputs implemented by the source's proved
`boundedConstructible_rightDerivedLowerShriek`; their separate Sheaf modules are not
imported. The new ordinary import `ProEtaleUnitLerayChainFormula` supplies the already
published `proEtaleUnitLerayDirectImageIso`, avoiding a duplicate coefficient-map proof.
Its node `lem-trf-proetale-unit-leray-chain-formula` is requested as a generic tool use:
only this underived coordinate isomorphism is used, with no trace-formula result.

Searches were repeated with `msearch.py`: LeanFinder (compact support and geometric-fibre
Tor amplitude), Loogle (`DerivedCategory.IsLE, DerivedCategory.IsGE`), and source/Mathlib
ripgrep. There is no exact Mathlib theorem; the source finite projection formula and
finite-truncation amplitude lemmas give the direct proof used here. Edge cases are
covered uniformly: zero ring, empty source or target, dimension zero, equal interval
endpoints and positive tower exponent one require no additional hypotheses.

The resumed compile exposed expensive automatic unfolding of `Etale.derivedTensor` and
broad simplification through the global-sections ring. A local irreducibility attribute
(as used by the existing source consumers) and explicit natural-cast rewrites remove
those elaboration costs. No imported definition or global instance is changed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
