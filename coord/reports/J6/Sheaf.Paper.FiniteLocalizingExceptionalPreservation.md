## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible` in `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` with a complete proof from named library results and one separate smooth lemma. Existing declaration signatures, definitions and public imports are unchanged. No source-library file was edited.

The arbitrary-map part is proved: identify the ordinary finite-coefficient property, compare compactifications on etale-origin objects, transport the existing ordinary restricted adjunction across the coefficient equivalences, and use shifted generators to identify the given large right adjoint on Dctf. Restrict the GIVEN adjunction by fully faithful inclusions and verify that its Hom equivalence is literally the specified one.

The existing source preservation theorem follows closed support, smooth tensor duality, affine charts and gluing, so the unit's mathematical route is retained. The generic generator comparison is already completely proved in the private helper `AdjunctionTransfer.rightAdjoint_preserves_generators`; `import all` accesses that helper without using the downstream public transfer theorem.

Added `Sheaf.Paper.FiniteLocalizingSmoothLocalFormula` for the genuinely separate final smooth tensor calculation. Its hypothesis includes smoothness, and its conclusion contains neither arbitrary-map preservation nor restriction of the adjunction. The original theorem combines this result with the proved preservation and restriction argument.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible` (`sk-prop-sf-rf-shriek-preservation`). Its proof body contains zero `sorry`.

Added hole: `AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_smoothLocalFormula` (`lem-sf-finite-localizing-smooth-local-formula`), exactly one `:= by sorry` in its own module. Total delivered holes: one. This is a decomposition (one hole closed, one added; net zero), not a claim that the entire original result is proved without a new assumption. The preservation and specified-adjunction restriction portions are complete Lean proofs.

All private helpers are proved. No definition contains a hole. The smooth remainder requires constructing a natural isomorphism of functors, using a single common cover trivializing both rank-one lines. The existing objectwise smooth formula alone does not supply this final coherence. Scratch work tested derived coefficient-pullback transport successfully; the attempted concrete tensor-map naturality proof required expensive unfolding and was not included.

Validation: `lcompile.py --all` compiled both delivered modules in dependency order. Its two style warnings were corrected. Final delivery preflight checks the complete packet again.

## No longer needed

The following direct proof imports were removed; public imports were preserved:

- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport`
- `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.OpenTorBoundArbitraryField`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SfAffineChartFactorizationGluing`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`
- `Sheaf.Paper.FiniteProperLocalizing`

Most of these remain transitive imports of the ordinary source theorems, the encoding equivalence, or the separate smooth lemma; this delivery does not claim they are globally pruned or withdraw any module. In particular, the adopted source library and all its declarations are preserved.

The separate planned bounded-below telescope proof is unnecessary here: the existing ordinary source theorem already supplies the small adjunction. Likewise, the separate chart-comparison, closed-support Tor-bound and open-Tor modules are not directly applied: those mathematical steps are already implemented in the source theorem's affine-chart proof. The small-to-large comparison uses the existing generic cone/orthogonal argument, with the exact recorded localizing closure, rather than assuming compactness of generators.

Parent proof-dependency entries no longer directly used are:

- `det-ctf-finite-proper-localizing`
- `lem-asd-finite-etale-twist-line`
- `lem-sf-etale-proetale-exceptional-transport`
- `lem-sf-localizing-hom-test`
- `lem-sf-smooth-dualizing-complex-invertible`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`

The etale/pro-etale transport, tensor-pullback comparison, and localizing Hom test remain dependencies of the new smooth lemma. The finite-proper-localizing result remains elsewhere in the source import closure. Thus no whole-module withdrawal is requested, and no global module-pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The plan did not exploit the already proved ordinary preservation and Dctf adjunction in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness`. Reusing it avoids redoing the closed/smooth/chart calculations while retaining that route.

There are two localizing-closure conventions in the library. The generic helper used here works with the exact `CategoryTheory.localizingClosure` in the item. The separate `ObjectProperty.localizingClosure` Hom-test theorem indexes coproducts in the Hom universe, whereas this item's closure records the ambient object universe; silently identifying those definitions would be incorrect. The imported private helper proves the appropriate version directly, so no such identification is made.

No existing statement was disputed or changed. No forced adaptations or change records are required. The first preflight rejected the missing LeanSearch kind (LeanFinder and Loogle count as one kind) and an added file-level elaboration option. Added the actual LeanSearch result and scoped the option to the theorem; the existing module interface then compares identically.

## New nodes

`lem-sf-finite-localizing-smooth-local-formula` separates the final common-cover smooth formula from arbitrary-map preservation and adjunction restriction. Its source is the final paragraph of the same blueprint proof. Its module states the common cover, trivialization of the actual comparison-pulled-back Tate line, and natural shifted-pullback formula. The docstring gives the complete proof route and checks dimension zero, the zero ring, and the empty scheme. This is the sole new node and sole remaining delivered hole.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
