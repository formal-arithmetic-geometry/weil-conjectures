## What changed

Proved `AlgebraicGeometry.proEtale_restriction_injectives` with its original signature,
universes and all five conclusions. The proof uses the existing concrete pro-etale slice
equivalence, the source library's localization adjunction and exact Kan extension,
its injective-preservation instance, and the unbounded right-derived composition API.
The derived comparison is explicitly normalized by the required unit equation.
No definitions, statements, instances, or public reexports were changed.
The item's node now records this shorter route. Its obsolete direct weak-etale permanence
tool approval is removed because that argument is encapsulated by the proved slice API.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.proEtale_restriction_injectives`
(node `lem-weil-pbc-proetale-restriction-injectives`). Added 0 holes; split off 0 theorems.
There are no `sorry`s left in the delivered Lean file. Single-file compilation succeeds.
The explicit `#print axioms` check reports only `propext`, `Classical.choice`, and `Quot.sound`.
The delivery tool also checks every declaration's axioms.

## No longer needed

Removed all sixteen private proof imports:

- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Category.ModuleCat.Ulift`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.Paper.SiteRestrictionInjectives`
- `Sheaf.RingTheory.IndEtaleStability`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`

The proof does not need the following former direct proof dependencies:
`def-weil-extension-by-zero-presheaf`, `def-weil-pbc-etale-sum-extension`,
`def-weil-pbc-proetale-modules`, `def-weil-pbc-proetale-operations`,
`def-weil-pbc-proetale-site`, `def-weil-presheaf-modules-sheafification`,
`def-weil-sheaf-of-modules-category`, `lem-trf-weakly-etale-between-objects`,
`lem-weil-pbc-ind-etale-stability`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-site-restriction-injectives`, and `prop-weil-pbc-proetale-constant-exact`.
The explicit site definition and coefficient/operation definitions remain statement
vocabulary; they are not additional proof obligations here. The general ringed-module
construction and abelian-sheaf detour are unnecessary because the existing source
localization API works directly for `ModuleCat Λ`. Weak-etale permanence is encapsulated
by the already proved slice-equivalence module. The derived-category machinery already
supplies descent from K-injectives, so a second descent argument is unnecessary.
Existing public reexports are preserved; this list asserts local proof independence,
not that every named module leaves every target's import closure.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-module construction and transport from underlying abelian sheaves
are redundant for the stated `Sheaf ... (ModuleCat Λ)` interface. The source theorem
`SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian` already handles
arbitrary weakly etale maps, and the source injective-preservation instance needs no
monomorphism. The left adjoint is therefore constructed directly with
`sheafPullbackConstruction`, bypassing the named `localizationLowerShriek` interface's
unnecessary monomorphism binder. All schemes, coefficient rings, and unbounded complexes
allowed by the original statement remain covered. The node is not a realized statement
or step of `dag/units/sk-thm-properbasechange.json`; the unit route is preserved.

The coefficient-independent slice clause also applies when the ring is zero or
noncommutative and when W is empty. No finiteness, commutativity, boundedness, or
monomorphism assumption was added.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
