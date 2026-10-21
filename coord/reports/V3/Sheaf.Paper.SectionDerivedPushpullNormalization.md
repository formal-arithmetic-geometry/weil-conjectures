## What changed

Proved `AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionDerivedPushpullNormalization`
from the existing exact-derived comparison, exact-derived mate and ordinary normalized
adjunction-comparison APIs. The declaration and `normalizationInternalAdjunction` keep their
original signatures and definitions. Private proved helpers check representative equations,
transport of adjunction mates and composition. No other Lean module is changed.

The ordinary pushforward compositor calculation checks the actual geometric underlying sheaf
map; its internal-module calculation reuses the existing private argument in
`Sheaf.Paper.ProfinitePointPullback`. Pullback coherence follows by the normalized adjunction
comparison theorem, and derived coherence follows by exact-square localization and transport.
The final pushforward coherence follows by mate pasting.

Updated the existing node's proof, proof dependencies and proof origin to record this route.
Removed unused tool-use approvals, preserving the order of those retained.

Preflight classifies the new helper-section parameter commands as a command-surface
change. The required record is
`coord/changes/V3-section-derived-pushpull-helper-scopes.md`; it lists all nine downstream
modules and explains why no public signature or consumer adaptation changes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionDerivedPushpullNormalization`.
Added zero holes; zero split-off statements. No `sorry` remains in the delivered module.
Dependencies with their own existing holes are used as the stage-3 brief prescribes.

Validation: the complete module compiled on the project server in 48.5 seconds with no
errors or warnings. The delivery wrapper runs compilation and preflight again before pushing.

## No longer needed

Removed direct proof imports:

- `Sheaf.Topology.ProfiniteCondensedRing`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.Paper.SectionModuleOperationsData`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.ProjectionMateExact`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`

The proof does not use the previously planned nodes
`lem-derived-exact-equivalence-squares`,
`lem-sfb-resolving-derived-adjunction-normalization`,
`lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-kinjective-hom-derived`,
`prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-termwise-adjunction-homotopy`, or
`lem-weil-pbc-localization-universal-property` as direct dependencies. Their matching
`tool_uses` entries were removed. Existing exact-derived APIs already supply the required
comparison identities and adjunction compatibility, so a second resolution construction
is unnecessary. This is local dependency pruning; existing consumers elsewhere still retain
whatever they need. No source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan reconstructs resolution comparisons and resolving adjunctions even
though the existing derived-functor composition and exact-derived mate APIs identify the
specified constructions directly. No statement repair was necessary. The blueprint unit's
route is preserved; only the argument below this node is shortened.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
