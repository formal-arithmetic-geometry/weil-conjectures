# CategoryTheory.UnboundedSectionsLocalization.modulesGrothendieck and restrictionAdditive

## Reason
The proof replaces the independent-universe Grothendieck transport instance with the
proved common-universe `SheafOfModules.isGrothendieckAbelian` theorem, and proves
restriction additivity by sectionwise extensionality. The public imports that existed
only for the old proofs are pruned. The declarations' signatures and meanings are
unchanged.

## Old
```lean
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses J R

instance restrictionAdditive (W : C) : (SheafOfModules.overFunctor.{u} R W).Additive :=
  (Classical.choose_spec
    (localized_restriction_adjunction R W (module_overFunctor_preservesZero R W))).2.2.1
```

## New
```lean
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian R

instance restrictionAdditive (W : C) : (SheafOfModules.overFunctor.{u} R W).Additive := by
  constructor
  intro M N f g
  ext V x
  rfl
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization | A8 | proof and imports updated together |

`python3 tools/downstream.py Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`
reported zero downstream modules. No consumer adaptation is required. No target
statement or definition used by a target changes.

The removed public imports are `Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`, and
`Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`. The direct public
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` import supplies the
homology functor used by the existing statement.

## Status
landed 20261018T150144-L-3798734 2026-10-18 (merge of deliver/A8/Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization)
