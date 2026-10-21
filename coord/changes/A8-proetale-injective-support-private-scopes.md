# proEtaleInjectiveSupportGlobalModel

## Reason

The delivery fills the theorem using private local helpers. Static preflight classifies
new top-level `variable`, `include`, `omit`, and local `attribute` commands as an
interface-affecting change and requires this record. These commands only scope the
new proved private helpers. No existing public declaration or instance is changed,
and all existing public imports remain verbatim. There is no mathematical statement
or definition repair.

## Old

The public declaration was:

```lean
theorem proEtaleInjectiveSupportGlobalModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    ∃ adj : lowerStar (ModuleCat.{u + 1} A) i ⊣ finiteClosedUpperShriek A i j,
      adj.counit = supportModelInclusion A i j hPair ∧
      (finiteClosedUpperShriek A i j).PreservesInjectiveObjects ∧
      ∃ c : finiteClosedUpperShriek A i j ⋙
          Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ≅ supportSections i A,
        (∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
          c.hom.app M ≫ kernel.ι (M.obj.map (supportRestrictionArrow i).op) =
            (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).inv.app
                ((finiteClosedUpperShriek A i j).obj M) ≫
              (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
                ((supportModelInclusion A i j hPair).app M) ≫
              (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
                (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M) ∧
        ∃ e : (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus ⋙
            (Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≅ derivedSupportSections i A,
          ∀ I : HomotopyCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
            (∀ r : ℤ, Injective (I.obj.as.X r)) →
            (∀ n : ℤ, CochainComplex.IsStrictlyGE I.obj.as n →
              CochainComplex.IsStrictlyGE
                (((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                  I.obj.as) n) ∧
            (∀ r : ℤ, Injective
              ((((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                I.obj.as).X r)) ∧
            IsIso ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ∧
            IsIso ((Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I)) ∧
            IsIso ((supportSections i A).rightDerivedFunctorPlusUnit.app I) ∧
            (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I) ≫
              (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
                ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ≫
              e.hom.app (DerivedCategory.Plus.Qh.obj I) =
              DerivedCategory.Plus.Qh.map
                ((Functor.mapHomotopyCategoryPlusCompIso c).hom.app I) ≫
                (supportSections i A).rightDerivedFunctorPlusUnit.app I := by
  sorry

```

There were no section variables or local irreducibility attributes between the
namespace command and this declaration.

## New

The public declaration retains exactly the same signature:

```lean
theorem proEtaleInjectiveSupportGlobalModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    ∃ adj : lowerStar (ModuleCat.{u + 1} A) i ⊣ finiteClosedUpperShriek A i j,
      adj.counit = supportModelInclusion A i j hPair ∧
      (finiteClosedUpperShriek A i j).PreservesInjectiveObjects ∧
      ∃ c : finiteClosedUpperShriek A i j ⋙
          Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ≅ supportSections i A,
        (∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
          c.hom.app M ≫ kernel.ι (M.obj.map (supportRestrictionArrow i).op) =
            (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).inv.app
                ((finiteClosedUpperShriek A i j).obj M) ≫
              (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
                ((supportModelInclusion A i j hPair).app M) ≫
              (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
                (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M) ∧
        ∃ e : (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus ⋙
            (Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≅ derivedSupportSections i A,
          ∀ I : HomotopyCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
            (∀ r : ℤ, Injective (I.obj.as.X r)) →
            (∀ n : ℤ, CochainComplex.IsStrictlyGE I.obj.as n →
              CochainComplex.IsStrictlyGE
                (((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                  I.obj.as) n) ∧
            (∀ r : ℤ, Injective
              ((((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                I.obj.as).X r)) ∧
            IsIso ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ∧
            IsIso ((Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I)) ∧
            IsIso ((supportSections i A).rightDerivedFunctorPlusUnit.app I) ∧
            (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I) ≫
              (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
                ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ≫
              e.hom.app (DerivedCategory.Plus.Qh.obj I) =
              DerivedCategory.Plus.Qh.map
                ((Functor.mapHomotopyCategoryPlusCompIso c).hom.app I) ≫
                (supportSections i A).rightDerivedFunctorPlusUnit.app I  := by
  -- Complete proof in the delivered module; zero sorry.
```

The private helpers are scoped by these section variables:

```lean
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range i) (Set.range j))
```

Local irreducibility attributes prevent elaboration from unfolding the star functors
and the private kernel/adjunction helpers. `include hPair` and `omit` commands specify
the necessary hypotheses of the new private lemmas. Local linter configuration is
used for the reused private vanishing lemma. These local commands do not export any
notation, attribute, instance or declaration to importers. The named theorem binds all
of its own original variables explicitly; its source signature was compared verbatim
with the base and is unchanged.

The only new proof import is
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`.
Five unused private proof imports are removed as listed in report.md. Public imports
are identical to the base.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel | A8 | Its sole public theorem keeps its exact statement and now has a complete proof. New helpers are private. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel --uses
proEtaleInjectiveSupportGlobalModel` reports zero downstream Lean modules and only the
item's own declaration as a textual user. No consumer adaptation is necessary. This
absence of current importers is not a withdrawal: the item and its Lean attachment
are retained for its unfinished DAG parents. Target statements and definitions are
unchanged.

## Status

landed 20261021T110924-L-3808875 2026-10-21 (merge of deliver/A8/Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel)

The final single-file remote compile passed in 19.9 seconds with no diagnostics.
The first delivery preflight requested this change record and pushed nothing. This
record completes that packet requirement; the theorem proof and signature are unchanged
from the successfully compiled version.
