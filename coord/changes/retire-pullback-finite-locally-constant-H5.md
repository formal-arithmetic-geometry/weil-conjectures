# AlgebraicGeometry.Scheme.pullback_finite_locally_constant

## Reason

Complete the depth-zero retirement item in `coord/retire-items.tsv`, under the human's
handoff in `coord/changes/retire-sheaf-twins-20261020.md`. The Sheaf copy already has
zero textual proof holes. Its upstream twin proves the same theorem using the canonical
`IsFiniteLocallyConstantSheafOfTypes` predicate. `IsLisseEtaleSheafOfSets` is an abbreviation
of that predicate, so both signatures below are definitionally equal, including universes.
The upstream private isomorphism-transport helper likewise accepts the exact old signature.
No source-library file changes.

## Old

In `Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`:

```lean
theorem pullback_finite_locally_constant {T Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (f : Y ⟶ T) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLisseEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) :
    Nonempty (((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F) ≅
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) ∧
    IsLisseEtaleSheafOfSets
      ((sheafCompose Y'.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F))
```

The two `import all` consumers also use this private helper:

```lean
private theorem finiteLocallyConstant_of_iso {X : Scheme.{u}}
    {G H : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : G ≅ H)
    (hG : IsLisseEtaleSheafOfSets G) :
    IsLisseEtaleSheafOfSets H
```

## New

Withdraw the Sheaf copy through `deleted.txt`; use the existing declarations in
`WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant`:

```lean
theorem pullback_finite_locally_constant {T Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (f : Y ⟶ T) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) :
    Nonempty (((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F) ≅
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) ∧
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y'.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F))
```

```lean
private theorem finiteLocallyConstant_of_iso {X : Scheme.{u}}
    {G H : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : G ≅ H)
    (hG : IsFiniteLocallyConstantSheafOfTypes G) :
    IsFiniteLocallyConstantSheafOfTypes H
```

Each of the four active direct consumers changes only its import's module prefix from
`Sheaf` to `WeilConjectures`; both `import all` modifiers are preserved. All consumer
statements, proofs, attributes and other imports remain byte-for-byte unchanged.
The exact old signatures are checked in a scratch Lean module by direct application
of these upstream theorems. Empty schemes, empty covers and empty stalks are allowed
in both versions; no additional hypotheses are introduced.

The node `lem-weil-pbc-pullback-finite-locally-constant` points to the upstream theorem.
Its proof description records the upstream implementation's already proved comparison
from algebraically closed stalks to the predicate at all separably closed stalks
(`lem-galois-finite-stalks-comparison`). The stratum node's proof names the new provider
of the private helper. No parent dependency is removed: every parent continues to use
the same theorem through its canonical upstream provider. The unit route is preserved.
No target statement or definition changes, so no target statement review is reopened.

## Users

`tools/downstream.py` lists five active downstream modules. The first four are direct
importers and are delivered together; the fifth is unchanged and checked against the
compiled overlay. Searches in both Lean roots and quarantine find no further direct
importer. All five are unclaimed when checked for this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum | unclaimed | Replace private import all; preserve proof. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Replace private import all; preserve proof. |
| Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement | unclaimed | Replace private import; preserve proof. |
| Sheaf.AlgebraicGeometry.LisseStratumInteriors | unclaimed | Replace private import; preserve proof. |
| Sheaf.AlgebraicGeometry.IrreducibleLisseStrata | unclaimed | No source edit; compile unchanged against migrated dependency. |
| Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant | H5 | Withdraw duplicate module with zero textual holes. |

## Status

landed 20261021T002935-L-1581010 2026-10-21 (merge of deliver/H5/Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant)
