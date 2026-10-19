## What changed

Proved `AlgebraicGeometry.Etale.smooth_exceptional_base_change` with its exact original
signature and definitions. Identified its canonical comparison with the existing upstream
exceptional mate, used the existing smooth base-change isomorphism, and proved tensor
compatibility by transposing projection exchange, specializing to the unit, and applying
braiding naturality. All private helpers have complete Lean proofs. No public declaration
is added or changed. Updated the node proof to this route. The local smallness instance
now reuses `Scheme.Etale.essentiallySmall`, avoiding a duplicate exported declaration.
The local attributes and private-helper universes are documented in
`coord/changes/Y6-smooth-exceptional-proof-context.md`; no consumer needs adaptation.

The retained attempt did not compile despite its old report. Repaired missing naturality
lemma names by applying naturality directly, made the tensor-mate helper generic in its
coefficient category to avoid a kernel timeout, and expanded the canonical tensor and
isomorphism equations explicitly in the final simplification.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Etale.smooth_exceptional_base_change`
(node `prop-asd-smooth-base-change`). Added zero holes; split off zero theorems. The
delivered module contains no `sorry`. The proof uses the already stated upstream theorem
`isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`, which remains
`by sorry` in the unchanged upstream module; this delivery does not claim that dependency
is proved. Its tensor compatibility is proved here from existing projection exchange.

The retained complete proof compiled with exit code 0 in 34.9 seconds; its pruned module
compiled in 33.2 seconds. On resuming on 2026-10-19, the delivered module compiled again
with exit code 0 in 30.3 seconds. After replacing the named local instance with the
existing theorem, it compiled with exit code 0 in 36.1 seconds. The import-direction
checks for SmoothDuality and
LowerShriekProjectionExchange both passed. The current server build also compiled the
unchanged delivered proof with exit code 0 in 31.5 seconds on 2026-10-19.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ProperOpenSection`
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.DerivedGlobalGerm`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.CompactificationCategory`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale`
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`
- `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`

These original proof dependencies are unnecessary as direct inputs to this shorter route:

- `def-weil-pbc-etale-shriek-base-change-map`
- `lem-amb-etale-adjoint-locality`
- `lem-amb-proper-coproducts-projection`
- `lem-amb-unbounded-compact-support-comparisons`
- `lem-asd-etale-compact-support-normalization`
- `lem-asd-etale-finite-twist-pullback`
- `lem-asd-ordinary-finite-p1-adjunction`
- `lem-pur-etale-open-derived-tensor`
- `lem-weil-pbc-etale-cover-detects-iso`
- `lem-weil-pbc-etale-shriek-base-change-modules`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `prop-weil-pbc-inverse-image-modules-exact`
- `sbc-thm-etale-local-normal-form`
- `thm-nagata-compactification`

Removed obsolete tool approvals (their relative order is otherwise preserved):

- `lem-weil-pbc-proper-open-section`
- `lem-weil-pbc-etale-shriek-base-change-modules`
- `lem-kun-proper-base-change-torsion-ring`
- `lem-weil-pbc-extension-by-zero-stalks`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-geometric-point-pullback-stalk`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `prop-nagata-compactification-category`
- `def-kun-unbounded-exchange`
- `thm-nagata-compactification`
- `lem-weil-pbc-etale-restriction-injectives`
- `def-weil-pbc-etale-shriek-base-change-map`
- `lem-pc-kflat-resolution`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `sbc-thm-etale-local-normal-form`
- `lem-weil-pbc-etale-cover-detects-iso`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-amb-unbounded-compact-support-comparisons`
- `lem-pur-etale-open-derived-tensor`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`

No modules are withdrawn. These dependencies may remain needed through other routes; no
claim is made that their whole import closures disappear.

## Where the brief, the DAG or earlier work was wrong

The previous report incorrectly claimed a clean compilation. Its file retained debugging
options and failed elaboration. The upstream library already states the smooth exceptional
base-change isomorphism for the canonical map; it is a strict component of this module's
conjunction, not a new restatement of the whole goal. The additional tensor compatibility
is a real proof here. The unit's `realized` statement and step lists are empty, so the
shorter node-level argument does not remove a realized unit step.

Two required dry-run attempts crashed before preflight: the launcher's internal temporary
worktree `git checkout -q --detach origin/sheaf-dag` exceeded its 600-second timeout.
The resumed dry run cleared its worktree-capacity queue but correctly rejected a named
local instance because its declaration was public. Replaced that duplicate construction
with `attribute [local instance] Scheme.Etale.essentiallySmall`, whose existing proof is
identical. Launcher scripts were not modified.

The fresh dry run required a change record for added local attributes and universe
commands after the duplicate-instance repair. Added the record with all 349 transitive
importers and the unchanged effects on the three textual consumers. No public signature,
definition body or public import changed.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
