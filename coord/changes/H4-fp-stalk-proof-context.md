# Sheaf.CategoryTheory.Sites.FpStalkRealization: proof elaboration context

## Reason

The proof uses Mathlib's varying-ring module colimits and categories of elements.
Unrestricted unification repeatedly unfolds their constructions. Proved private
APIs and scoped transparency settings let subsequent proofs use their values on
section germs. The stage-3 interface scanner treats the additional commands as
potential interface changes, so this record documents their scope.

All existing public declaration signatures, construction bodies, and public
imports are verbatim unchanged. No target or definition changes meaning. No
existing public declaration acquires another universe or implicit parameter.

## Old

```lean
set_option autoImplicit false

universe u
```

There were no private-helper sections, scoped helper options, or helper attributes.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
```

These are module elaboration options, not exported options. The extra universe is
used only by the private `covering_refinement`, `moduleGerm_sum_smul`, and
`presentationCokernelIso` helpers.

The following new generic private declarations have `omit [HasFiniteLimits C] in`:
`finiteFreeIso`, `finiteFreeIso_basis`, `linearMapConjugacy`, `presentationCokernelIso`,
`colimitOverMap`, `colimitOverMap_germ`, `colimitOverMap_bijective`, `colimitOverComparison`,
`colimitOverComparison_germ`, `colimitUnitMap`, `colimitUnitMap_germ`, `colimitUnitIso`,
`colimitUnitIso_germ`, `colimit_matrix_lift`, `pointOverFiberIso`, `modules_map_germ`,
`moduleGerm_sum_smul`, `modules_freeHomEquiv_germ`, `moduleRestrictionIso`, `moduleComparison`,
`moduleComparison_germ`, `unitRestrictionIso`, `moduleUnitIso`, `moduleUnitIso_germ`,
`freeModuleImageIso`, `freeModuleImageIso_basis`, `matrixSection_val`, `matrixHom_spec`.

The private-helper section registers the proved private helpers
`fastRingSheafCompose`, `fastAbelianSheafify`, `fastSetSheafify`,
`fastRingAbCompose`, and `fastAbSetCompose` with local instance priority 20000.
They prove existing sheaf-composition and sheafification propositions using
Mathlib's instances. This caches their proof search; it adds no mathematical
hypothesis or data. All five registrations end with `section Proofs`. The final
theorem introduces these properties explicitly only inside its proof body, for
the original and localized topologies.

A separate `section RealizationProof` contains only the final theorem. It assigns
local instance priority 11000 to the existing public Mathlib instance
`hasSheafCompose_of_preservesLimitsOfSize`. This avoids the expensive multicospan
instance search while elaborating the unchanged public signature. The priority
is not exported; no private constant appears in an existing public signature or
construction body.

The private definitions `colimitOverMap`, `colimitOverComparison`, `colimitUnitMap`,
`colimitUnitIso`, `moduleComparison`, `localizedModuleComparison`, `moduleUnitIso`,
`freeModuleImageIso`, `localizedFreeIso`, `matrixSection`, `matrixHom` are marked `irreducible`
after proving their germ, basis, or section-value APIs. No existing definition receives this
attribute.

The declarations `moduleRestrictionIso`, `moduleComparison`, `moduleComparison_germ`,
`localizedModuleComparison`, `localizedModuleComparison_germ`,
`localizedModules_preservesFiniteColimits`, `unitRestrictionIso`, `moduleUnitIso`,
`moduleUnitIso_germ`, `localizedFreeIso`, `localizedFreeIso_germ`, `matrixSection`,
`matrixSection_val`, `matrixHom`, `matrixHom_spec`, `matrixHom_basis`, `matrixHom_conjugacy`
have the scoped options:

```lean
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
```

The final theorem uses those two settings only inside its proof body. They keep
unification from unfolding the private colimit constructions when their proved
APIs suffice. The basis lemma has a scoped heartbeat bound of 100000. The final
theorem has a scoped heartbeat bound of 800000, with an explanatory comment for
the cokernel assembly. Neither changes the compile server's wall-time limit.

The linear colimit comparison is first proved for abstract presheaves of modules
over a ring diagram. Its naturality follows from the additive finality comparison
through the faithful forgetful functor. Explicit identity isomorphisms of restricted module presheaves and unit presheaves
specialize the comparison and unit-stalk isomorphisms to sheaves and the site. The
fiber comparison is similarly proved first for an abstract Mathlib site point.
The finite-free coproduct comparison, matrix conjugacy, and cokernel transport
are checked for abstract functors, modules, and categories before specialization. All these private helpers are proved.

Comparison and unit maps use `ConcreteCategory.ofHom` on existing module bundles.
The matrix basis proof supplies the bundle's existing additive and scalar actions
explicitly, gives the ring and index of each free generator, and specifies
the free-section index type `I := ULift.{u} (Fin b)`. Its sum uses the existing bundle's
`AddCommMonoid` instance explicitly. These choices avoid inferring
module data by unfolding colimit or free-sheaf constructions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | F2 | Imports the unchanged public interface. Its unfinished proof plans to use this theorem. No source adaptation is needed. |

The consumer check included the direct importer and
`tools/downstream.py --uses exists_fp_stalk_realization`. There is no current
textual call of the theorem, because the parent's proof is unfinished; the planned
dependency remains. No adapted module is included. The maintainer's independent
reader and global build verify the consumers after delivery.

## Status

landed 20261020T211728-L-3494562 2026-10-20 (merge of deliver/H4/Sheaf.CategoryTheory.Sites.FpStalkRealization)
