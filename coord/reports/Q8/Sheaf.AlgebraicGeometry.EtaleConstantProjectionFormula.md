## What changed

Proved `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_finite_torsion_cd` with its original signature, for all unbounded E and K and any commutative torsion coefficient ring. Transfer the numerical torsion bound to module cohomology, apply the already proved arbitrary-coefficient coproduct theorem, and use the ring as a generator. Generic private helpers prove the derived tensor comparison commutes with shifts, the projection mate is exact and invertible at the tensor unit, and the generator criterion gives every component.

Repaired `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap` without changing any existing signature: explicit component evaluation, its reflexive identification and invertibility transfer are packaged once to prevent kernel expansion of the concrete derived tensor structures. No axiom, arbitrary data choice, or postponed definition proof is added. See `coord/changes/etale-constant-projection-components.md`.

Added proof-only imports for the actual proved source APIs and the existing module-cohomology comparison. The public imports match the current shared item, including its upstream `DerivedCategories` migration; the original docstrings remain. Updated both existing nodes to match the implementation. Two new nodes attach already proved source theorems; they add no Lean modules or holes.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_finite_torsion_cd` (`lem-kun-0f12`). Zero holes remain in the item. Zero holes are added anywhere; zero statements are split off. Every private helper is proved. The repaired map module already had zero holes and still has zero.

The existing imported `Scheme.nonempty_etaleModuleCohomology_forgetIso` is a proved source dependency. Its Sheaf twin was retired upstream during this session; the proof-only import now uses `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`, as its existing node records.

The full item compiled in 40.6 seconds after the generic torsion and integer-bound lemmas removed concrete-module kernel expansion. The cohomology forgetful comparison and natural-to-integer degree bounds are combined in a generic functor lemma; the numerical infimum bound is extracted generically as well. Earlier full checks exceeded 60 seconds; no limit was raised and no file was split to evade it. Five original direct consumers compile unchanged. `ExternalRHomConePairing` fails in its imports with duplicate `CategoryTheory.homComplexFunctor` from the upstream and Sheaf HomComplex modules; its original copied outside the sandbox overlay fails identically. No forced adaptations are delivered.

## No longer needed

No original public import is removed. The public DerivedCategories path follows its upstream migration. Removed the trial proof import `Sheaf.Paper.IntegralResidueDerivedMonoidal` and its `new-integral-residue-derived-monoidal` dependency: the generic unit proof now descends the specified tensor comparison directly through `Functor.OplaxMonoidal.ofLaxSquare`. The smaller generic monoidal, homotopy-map and unit API imports support that proof. This removes 208 modules from the whole import closure relative to that trial route; no global unreachability is claimed.

The proof-only imports removed from the current shared item are:

- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `WeilConjectures.CategoryTheory.DerivedModuleDirectSums`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The following former direct proof dependencies are pruned from this proof (some remain statement or transitive infrastructure elsewhere; no global unreachability is claimed):

- `lem-weil-pbc-module-sheaves-grothendieck-abelian` — `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `def-weil-pbc-global-sections-functor` — `Mathlib/source infrastructure`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-weil-pbc-module-sheaves-colimits-forgetful` — `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-weil-pbc-cohomology-filtered-colimit` — `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-pur-kinjective-degreewise-existence` — `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-kun-grothendieck-derived-coproducts` — `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-kun-finite-cd-acyclic-complex` — `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-pc-derived-module-direct-sums` — `WeilConjectures.CategoryTheory.DerivedModuleDirectSums`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `def-kun-constant-sheaf` — `Mathlib.Algebra.Homology.Additive`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-weil-pbc-ringed-projection-mate-exact` — `Sheaf.Paper.ProjectionMateExact`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-pc-sites-module-sheafification-interface` — `Mathlib/source infrastructure`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-pc-kflat-resolution` — `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `def-pc-kflat-complex` — `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `def-pc-flat-sheaf-modules` — `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `def-pc-tensor-complex-sheaves` — `Mathlib.Algebra.Homology.BifunctorShift`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-weil-pbc-site-derived-tensor-descent` — `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-kun-derived-tensor-direct-sums` — `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-sf-triangle-morphism-iso` — `Mathlib/source infrastructure`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.
- `lem-pc-derived-module-free-generation` — `WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration`. Its separate statement is unnecessary here: the proved source coproduct, derived tensor/adjunction, and generator APIs cover the corresponding step.

Removed all old `tool_uses` approvals except `lem-weil-pbc-etale-module-cohomology-forget`, in their original order. The approved nodes removed are exactly the old tool list minus that comparison. The source `ModuleCatGeneration` criterion replaces the cellular-filtration generation route; the source global-sections coproduct theorem replaces separately importing K-injectives, filtered-colimit and acyclic-complex statement modules. The generic closed derived tensor and projection APIs replace the separate ringed-site mate and tensor descent statements.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and true. The original DAG plan duplicated already proved source-library results: its claimed need for separately building arbitrary-coefficient coproduct preservation and module generation was unnecessary. The source `preservesCoproducts_rightDerivedGlobalSections` already accepts an arbitrary ring with a coefficient dimension bound, so no unjustified extension from Z/n is used.

The original component definition was definitionally correct but expensive for the kernel to compare with its abstract mate after concrete instances were inserted. The explicit evaluation package repairs that interface; every component is still the original mate, by reflexivity. Empty schemes, the zero ring, empty coproducts and unbounded complexes are covered by the generic proofs.

The unit record has empty `realized.statement` and `realized.steps`; its mathematical route is preserved. All pruning is below unit level.

The dispatcher reference clock reset during provider-error resumptions (earlier start 1792425536, current `.budget.start` 1792437874.358424); no attempt identifiers were exposed in the sandbox. Metadata was not edited. Work continued against the same item and sandbox.

The unrelated `ExternalRHomConePairing` baseline duplicate-import failure is recorded in the change record, with the original consumer unchanged.

## New nodes

`lem-kun-module-generator-isomorphism-test` attaches the existing proved `DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self` in `WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration`. It states the isomorphism test on the degree-zero free rank-one module, with exactness, shifts and coproduct preservation.

`lem-kun-finite-coefficient-dimension-global-coproducts` attaches the existing proved `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedGlobalSections` in `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts`. It states the arbitrary-coefficient dimension version actually applied, rather than the narrower Z/n theorem.

Both nodes are source attachments with complete proofs in words and the required Mathlib search kinds, not new assumptions. Change record: `coord/changes/etale-constant-projection-components.md`.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
