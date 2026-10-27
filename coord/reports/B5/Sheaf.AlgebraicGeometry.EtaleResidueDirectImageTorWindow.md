## What changed

Filled `AlgebraicGeometry.Etale.hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound`
in `Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow`, without changing its signature.
A proved private generic helper bounds the direct image tensored with any finitely presented
constant module. It compares unbounded heart cohomology with classical higher direct images,
applies `DerivedCategory.bounded_heart_amplitude`, and transports vanishing through
`isIso_finiteConstantProjectionMap`. The public theorem specializes to the residue module
and applies `residue_tor_amplitude_test`. Bounded constructibility supplies the upper bound
on K used by projection. The node now records this implementation. A local ring-instance
priority matches the residue criterion and keeps quotient elaboration efficient; see
`coord/changes/etale-residue-direct-image-local-instance.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound`
(node `lem-pur-etale-residue-direct-image-tor-window`).
Proved the private helper `AlgebraicGeometry.Etale.directImage_tensor_window`.
No holes added, no split-off statements, and no sorry remains in the delivered module.
The complete proof compiled in 35 seconds. Replacing haveI with have removed its sole
style warning; delivery compilation and axiom checks passed. The first preflight requested
a change record for the local instance-priority command, now included.

## No longer needed

Removed proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`

The tensor-unit test (`lem-kun-tensor-unit`) is unnecessary because bounded constructibility
already supplies K's upper cohomological bound. The explicit module-sheaf infrastructure
nodes `lem-weil-pbc-module-sheaves-grothendieck-abelian`,
`lem-weil-pbc-module-sheaves-enough-injectives`,
`prop-weil-pbc-kinjective-resolutions-exist`, and
`lem-weil-pbc-module-direct-image-left-exact` are unnecessary direct dependencies: the
ordinary ModuleCat-valued sheaf instances and lowerStar additivity are already provided
by the source derived-category framework. The separate negative-vanishing node
`lem-weil-pbc-derived-functor-negative-vanishing` is replaced by the existing unbounded
single-object lower bound in PlusCompatibility. Removed the corresponding obsolete tool
approvals from the node. PlusSingle remains a transitive proof dependency of the unbounded
comparison; its separate direct import is redundant. No source declarations or modules
are withdrawn. All public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid. Its Step 1 does more than necessary: the assumed bounded
constructibility of K already gives the upper bound needed for projection. Step 3's
Grothendieck, enough-injective and direct-image theorems use the SheafOfModules encoding;
the K-injective theorem is in the ordinary ModuleCat-valued encoding. None is required
directly: the source instance framework already supplies the structures used here.
The unit route, projection formula, finite heart induction and residue test are retained. Edge cases c = 0 and a = b require no changes;
all integer-to-natural conversions use the given c >= 0. No flatness or perfectness of
the residue module has been assumed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
