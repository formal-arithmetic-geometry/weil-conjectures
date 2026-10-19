## What changed

Proved eight of the eleven original holes in
`Sheaf.Paper.ModuleRingedToposDerivedComparison`, without changing any declaration
signature or definition. The ordinary exactness/flatness/K-flatness theorem uses
`InternalAbelianSheafModule.internal_section_tensor_comparison`; the signed braiding
identifies its right-sided acyclic test with `IsKFlatModuleObject`'s left-sided test.
For ordinary monoidal coherence, uniqueness of the pure-tensor and regular-unit
normalizations identifies the existing witnesses with the named comparisons.
`internalDelta_isIso` uses the existing general left-derived tensor comparison instance.
`mu_comparison` takes inverses of the isomorphism equality `delta_comparison`, and
the field-setting theorem specializes `delta_comparison` to the underlying morphism.
The proper projection equation uses the existing upstream
`Adjunction.rightAdjointProjectionMap_mate`: its tensor hypothesis follows from
`delta_comparison`, and its counit hypothesis follows by transposing
`derived_homEquiv` at the counit. Canonical currying comparisons translate the
existing uncurried interfaces. The open Hom equation localizes the existing ordinary
unit equation with `Adjunction.mapDerivedCategoryAdjunction_mate`, then uses
naturality and cancels the specified left-derived/levelwise comparison.
The open projection equation uses `Adjunction.projectionMap_mate`: its unit
hypothesis is `open_homEquiv` at the identity, and its tensor hypothesis follows
from `mu_comparison` by cancellation of explicit comparison isomorphisms.
Evaluation of the generic projection map is exactly the existing open projection
definition. Cancelling the extension comparison and the tensor of its inverse
finishes the displayed equation.
The only new proof import is
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat`.
No field, characteristic, finiteness, or separation hypothesis was changed.

The ordinary coherence and projection proofs need extra elaborator heartbeats to compare the generic
and specialized sheaf tensor constraints. The file compiles in 54.2 seconds with no errors or warnings using the standard
60-second limit. No compile tool or definition was changed. The resumed session repaired the
retained open-projection proof by cancelling the two comparison isomorphisms explicitly;
the tensor of inverse pullback comparisons carries its explicit `mapIso` witness.

## Proved and sorry left

Closed 8 original holes (all attached to
`lem-pd-module-ringed-topos-derived-comparison`):

- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.ordinary_exact_flat_kflat`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.ordinary_monoidal`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.internalDelta_isIso`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.mu_comparison`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.projection_comparison`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.open_homEquiv`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.openProjection_comparison`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.module_ringed_topos_derived_comparison`

Added 0 holes; split off 0 statements. Three original named theorem holes remain,
unchanged, on `lem-pd-module-ringed-topos-derived-comparison`:

- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.derived_homEquiv`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.delta_comparison`
- `AlgebraicGeometry.ProEtale.ModuleRingedComparison.composition_comparison`

The inverse tensor and projection equalities proved here still depend on the existing
`delta_comparison` hole. The ordinary clauses use existing stated dependencies,
which retain their own independently assigned proof obligations. This is a partial
proof delivery with no decomposition or new obligations.

## No longer needed

Removed the following redundant direct proof imports; the retained public interfaces
already expose all declarations needed by the proofs and statements:

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`
- `WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Sheaf.Paper.RingedTopoiTensorComparisonData`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Mathlib.CategoryTheory.Monoidal.Functor`
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.SectionModuleOperationsData`

No DAG node or module is claimed globally unnecessary: the three remaining clauses
still need their recorded arguments, and the removed direct imports remain available
through the existing public dependency interfaces. No unit statement or unit proof
step was bypassed. The completed clauses follow the corresponding existing node
steps, so the node's proof plan and dependency set need no route change.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was established. The existing ordinary comparison
already contains exactness, tensor coherence and flatness/K-flatness; it must be
specialized using uniqueness of the separately chosen normalized comparisons.
The K-flat definitions test opposite tensor orders, so merely projecting the existing
K-flat clause is insufficient: the signed complex braiding is needed in both directions.
For the inverse delta equation, working with explicit composite isomorphisms avoids
expensive inference of inverse morphisms of tensor functor images.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
