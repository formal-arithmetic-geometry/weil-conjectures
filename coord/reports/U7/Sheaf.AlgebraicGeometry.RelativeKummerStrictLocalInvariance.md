## What changed

Filled the proof of `AlgebraicGeometry.Etale.relativeKummer_strictLocal_invariance` in
`Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance`. The argument retains the unit's
rotated smooth-base-change square. Over Spec H, exact global sections and fully faithful constant
sheaves give the actual derived unit over Spec k. The mate identity transfers its invertibility
to each smooth curve. A derived-functor calculation identifies the resolution-defined global
pullback with the unit and Leray comparison. Explicit roots, tensor generators, and naturality
of the abelian Kummer sequence supply both normalization clauses.

Factored three existing definition bodies through constructed helpers with abstract coefficient
sheaves to share expensive type conversions. Two proved propositional witness helpers cache
the existing sheafification and Ext instances locally. All existing signatures and
mathematical maps are unchanged. The definition record is `coord/changes/U7-relative-kummer-map-sharing.md`.
No source-library file is modified.

Validation: the complete proof compiled in scratch validation in 46.3 seconds. The final
item and all six unchanged consumers compiled together, without warnings, against the
sandbox overlay. The consumers are NormalizedKummerCohomologyArrows,
NormalizedKummerGeneratorArrows, NormalizedKummerGlobalArrows,
RelativeKummerNormalizedStalks, Paper.KummerSiteCohomologyNormalization, and
Paper.RelativeKummerSiteNormalization. Their temporary sandbox copies were byte-identical
to the library and are not delivered. All original declaration signatures, public imports,
and declaration docstrings were checked unchanged.

## Proved and sorry left

Closed the single original theorem
`AlgebraicGeometry.Etale.relativeKummer_strictLocal_invariance`
(node `lem-pur-relative-kummer-strict-local-invariance`).
The item has zero `sorry`: one hole closed, zero added, zero split off.
All private helpers and the two propositional instance helpers have complete proofs.
No definition contains a hole.

## No longer needed

The direct imports removed from the item are:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison`
- `WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`

The original direct proof dependencies no longer needed by this route are:

- `def-pur-sheaf-tensor-product`
- `def-weil-pbc-scheme-conventions`
- `lem-pe-left-module-derived-evaluation-forget`
- `lem-sc-primitive-root`
- `lem-weil-pbc-cohomology-pullback-derived-unit`
- `lem-weil-pbc-cohomology-pullback-degree-zero`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-weil-pbc-constant-sheaf-sections-connected`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-weil-pbc-derived-plus-iso-on-cohomology`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-geometric-point-field-extension`
- `lem-weil-pbc-module-abelian-derived-direct-image-comparison`
- `lem-weil-pbc-module-abelian-inverse-image-comparison`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-strict-henselization-stalk-formula`
- `sbc-lem-affine-space-smooth`
- `sbc-lem-strict-henselian-constant-cohomology`

The strict-local stalk calculation, geometric-point extension, conservativity, and coefficient
forgetting of the derived exchange are replaced by exactness over the strictly local base and
the existing module-valued smooth-base-change theorem. The generic derived pullback calculation
works directly with module sheaves. Ordinary degree-zero and boundary naturality come from the
existing TorsorPullback and RootsOfUnityPullback APIs. Polynomial smoothness and localization
give the two structure maps directly.

The obsolete top-level `tool_uses` entries removed are exactly the nodes listed above,
except `def-pur-sheaf-tensor-product` and `def-weil-pbc-scheme-conventions`, which were
proof dependencies only. The corresponding smaller existing source APIs are used directly.

These are direct dependency and import removals. No declaration or module is withdrawn; some
of the listed modules remain available transitively or are needed by other items.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned strict-henselization stalk argument is longer than
necessary: the existing strict-local section-surjectivity and constant-sheaf unit results imply
exactness and full faithfulness directly. The existing derived smooth-base-change theorem
already accepts module coefficients. The updated node records this shorter argument while
preserving the unit's smooth-base-change route.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
