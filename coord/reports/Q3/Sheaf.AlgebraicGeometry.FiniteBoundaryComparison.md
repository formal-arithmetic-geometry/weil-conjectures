## What changed

Proved `AlgebraicGeometry.Etale.isIso_of_finite_boundary` in
`Sheaf.AlgebraicGeometry.FiniteBoundaryComparison`, with its existing signature and all
four public imports unchanged. The proof takes the cone in the ordinary unbounded derived
category, uses the existing arbitrary-module open-closed triangle to recover it from the
closed complement, composes derived direct images, and applies finite exact pushforward
zero-detection to every cohomology sheaf. The fully faithful inclusion reflects the resulting
isomorphism back to the bounded-below category. Properness remains a hypothesis.

All proof imports are private. Added imports for `OpenClosed.Derived`, `Finite.Counit`,
`RightDerivedFunctor.PlusCompatibility`, `RightDerivedFunctor.Comp`,
`RightDerivedFunctor.Triangulated`, and the source `DerivedCategory.HomologySequence`.
Updated the item's DAG proof, proof dependencies, origin, and obsolete tool approvals.
Three new DAG records attach already-proved source-library declarations; no Lean
module, declaration, intermediate hole or definition is added. No interface change,
consumer adaptation or change record is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_of_finite_boundary`
(node `lem-fin-finite-boundary-comparison`). Added 0 holes; split off 0 obligations.
No `sorry` remains in the delivered module, and no other Lean module is delivered.

Remote single-file compilation passes. A separate `#print axioms` probe reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; the probe is removed from the delivered file.
Thus this is a proof, not a decomposition resting on new or existing `sorry` declarations.
The proof covers arbitrary coefficient rings and empty schemes/fibres; in particular it
never chooses a geometric point in an empty fibre. No finiteness, torsion, quasi-compactness
of the open immersion, constructibility or Noetherian hypothesis was introduced.

## No longer needed

The following private imports were removed (their modules are no longer direct proof
dependencies of this item; they may remain needed by other parents):

- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The following original DAG proof dependencies are no longer directly used:

- `lem-weil-pbc-module-abelian-derived-direct-image-comparison`
- `lem-weil-pbc-derived-plus-iso-on-cohomology`
- `def-weil-pbc-derived-categories`
- `prop-weil-pbc-inverse-image-exact`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-closed-immersion-finite`
- `def-weil-pbc-inverse-image`
- `lemma-openclosed-stalk-upperstar`
- `lem-kun-04ca`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `def-weil-pbc-direct-image`
- `lemma-weil-pbc-finite-stalk-formula`
- `lemma-weil-pbc-geometric-stalk-conservative`

The coefficient-forgetting comparison and abelian essential-image recovery are unnecessary:
the proved source open-closed triangle already applies to `ModuleCat Λ`. The general
ringed-topos comparison is replaced by the proved functor-level K-injective composition
isomorphism. The bounded-below triangulation and cohomology checks are replaced by the
unbounded cone criteria and fully faithful inclusion. The closed-immersion finiteness step
is unnecessary: closed-support recovery already uses derived pushforward, and only `i ≫ b`
needs finite exactness. Stalk pullback, finite stalk products and stalk conservativity are
encapsulated in the proved source localization and finite-zero-detection results; they remain
transitive mathematical dependencies of those facts rather than new work for this item.
No unit statement or realized proof step is bypassed: `sk-prop-sf-cbc` has no fixed realized
steps here, and the original cone/support/composition/finite-stalk route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original DAG/docstring plan is mathematically valid but does not exploit the now-proved
source-library module-coefficient APIs. Its coefficient reduction and ringed-topos transport
are longer than necessary. The preserved original docstring is a historical proof plan;
the delivered Lean proof and updated DAG give the shorter implementation. No source error,
false statement, target change, definition repair or unavailable dependency was found.

The source declarations `exists_distTriang_openClosed`,
`isZero_of_isZero_lowerStar_of_isFinite`, and `rightDerivedFunctorCompIso'` had no exact
DAG attachment. Full DAG and blueprint searches found only differently typed statements
(e.g. finite-stage recollement, ringed-space composition), so the delivery records the
existing general declarations instead of restating them in Lean. Existing source facts
for unbounded triangulatedness and D⁺ compatibility already had nodes and are reused.

## New nodes

`lem-fin-module-open-closed-triangle`: the specialization of the existing proved
`AlgebraicGeometry.Etale.exists_distTriang_openClosed` to arbitrary `ModuleCat Λ`.
It records the open-closed cone triangle with its actual counit and unit. No new proof
obligation; source file `WeilConjectures.SixFunctors.OpenClosed.Derived`.

`lem-fin-finite-direct-image-zero-detection`: the specialization of the existing proved
`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_of_isFinite` to module sheaves.
It records finite pushforward reflection of zero via its epic counit, including empty fibres.
No new proof obligation; source file `WeilConjectures.SixFunctors.Finite.Counit`.

`lem-fin-kinjective-derived-composition`: the existing proved generic source construction
`CategoryTheory.Functor.rightDerivedFunctorCompIso'`, with the K-injective preservation
hypothesis retained. It supplies `Rb_*Ri_* ≅ R(bi)_*` using the existing sheaf composition
isomorphism. No new proof obligation; source file
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.

All three records have `lean.existing = true` and attach the existing source declarations;
none requires later proof or creates a Lean module. No change record was created.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
