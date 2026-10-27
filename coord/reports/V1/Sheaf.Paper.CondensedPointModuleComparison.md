## What changed

Filled all five proof holes of `Sheaf.Paper.CondensedPointModuleComparison` without
changing a declaration signature or the derived-comparison definition. The three instances
use the existing exactness instances for `mapMod`, the point adjunction, and additivity
from preservation of binary biproducts. Left exactness of the point inverse image is
obtained directly from the existing AB5/flat Kan-extension and sheafification instances.
Linearity follows from the module morphism axiom of the existing `mapModCompIso`, followed
by tensor interchange and cancellation of the inverse coefficient isomorphism. The derived
normalization follows from `mapDerivedCategoryNatIso_fac` and
`mapDerivedCategoryCompIso_fac`, cancelling the composition isomorphism. Updated the
item's DAG proof and proof dependencies to this route; no unit statement or step changes.

The only retained public imports are the existing Stalk and derived ExactFunctor modules.
Two private proof imports provide flat Kan-extension exactness and AB5 for abelian groups.
A private meta import supplies congruence-proof construction.
All existing docstrings are preserved. Private proved helpers expose the comparison's
hom transformation and combine the two factorization identities by inverse cancellation.
Local irreducibility annotations prevent unwanted expansion of the localization and
pullback constructions during elaboration. These annotations apply only inside this file
and change no public definition or attribute. The final conversion uses a local structural
congruence tactic adapted from `Sheaf.Paper.PerfectProjectionFormula`: the composite
functor's additivity proof carries the direct module preadditive instance, while the
stated derived comparison carries the abelian instance's inherited preadditive structure.
The tactic constructs a proof by congruence, proof irrelevance and definitional equality;
Lean's kernel checks the result. Explicitly reducing composite functor objects prevents
an irrelevant comparison between the source and intermediate site categories. Mathlib search was performed with LeanFinder,
Loogle and grep through msearch.py; local searches found the exact mapMod and derived
normalization APIs in the source library. No source-library file was changed.

Validation: all five proofs compiled together with lcompile.py in 11 seconds, with zero
`:= by sorry` bodies or new axioms. The final delivery performs its independent preflight.

## Proved and sorry left

Closed five original holes:

- `AlgebraicGeometry.ProEtale.condensedPointModule_preservesFiniteLimits`.
- `AlgebraicGeometry.ProEtale.condensedPointModule_preservesFiniteColimits`.
- `AlgebraicGeometry.ProEtale.condensedPointModule_additive`.
- `AlgebraicGeometry.ProEtale.condensedPointModule_comparison_linear`.
- `AlgebraicGeometry.ProEtale.condensedPointModuleDerivedComparison_normalization`.

All five belong to `lem-zl-condensed-point-module-comparison`. Zero holes added;
zero holes remain in the delivered module; no split-off lemmas or new modules.

## No longer needed

Removed these direct public imports because the declarations require only the existing
source-library constructions already exported by the retained imports:

- `Sheaf.Topology.ProfiniteCondensedRing`.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`.

Removed these private proof imports:

- `Sheaf.CategoryTheory.SiteInverseImageTensor`: direct AB5/flat Kan-extension exactness
  proves the required instance without its tensor/coherence package.
- `Sheaf.CategoryTheory.SheafTensor`: the established source-library sheaf tensor and its
  colimit-preservation instances already supply the mapMod instances' hypotheses.
- `Sheaf.CategoryTheory.ModuleObjects.LiftExact`: use the existing exact mapMod instances
  and preservation of binary biproducts directly.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`: the existing scheme-module
  pullback exactness instances already type-check the unchanged derived definition.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`: this Lean normalization
  concerns the actual internal module functors; no sectionwise transport is required.
- `Sheaf.CategoryTheory.ExactDerivedComposition`: use the source library's canonical
  composition iso and its normalization directly; its uniqueness theorem is unnecessary.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: normalization of the specified
  exact induced functors uses their existing factorizations directly, with no comparison
  against a separately chosen derived-functor presentation.

The following old proof dependencies are unused and removed from the item's proof route:
`lem-weil-pbc-left-exact-site-inverse-image-tensor`, `sk-def-sfb-sheaf-tensor`,
`det-prop-sfb-module-pullback-exact-lifted`,
`lem-sfb-restricted-transport-comparison-linear`,
`det-prop-sfb-module-pullback-exact-main`,
`lem-sfb-internal-module-operations-transport`, and
`lem-weil-pbc-exact-functor-derived-functor`. The general condensed-ring node
`sk-def-sfb-condensed-ring` is no longer a proof dependency: the unchanged statement
already takes the ring object and its structures as arguments. It remains a statement
dependency. Their reasons are the direct constructions
and calculations above. `def-weil-pbc-internal-abelian-sheaf-module-equivalence` and
`def-weil-pbc-proetale-operations` remain statement dependencies describing the
interpretation of the internal module categories, but are not used by these proofs.
Removed the corresponding obsolete `tool_uses` approvals for
`sk-def-sfb-sheaf-tensor`, `det-prop-sfb-module-pullback-exact-lifted`,
`lem-sfb-restricted-transport-comparison-linear`,
`det-prop-sfb-module-pullback-exact-main`,
`lem-weil-pbc-exact-functor-derived-functor`, and
`lem-sfb-internal-module-operations-transport`.
The generic exact-derived composition node remains needed through the existing
canonical composition iso. No declaration or module is withdrawn. These are dependency
prunings from this item, not a claim that all those modules have no other consumers.

The interface-pruning change record is
`coord/changes/V1-condensed-point-comparison-imports.md`. No current Lean importer needs
adaptation. The DAG parent remains attached.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The planned argument asks for several general
transport theorems whose conclusions already have direct source-library implementations.
The shorter proofs specialize those existing constructions and retain the specified
coefficient map and comparison. Unrestricted schemes, arbitrary commutative condensed
coefficients, and all unbounded complexes are kept. No flatness, boundedness, finiteness,
or nonempty-site assumptions were introduced.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
