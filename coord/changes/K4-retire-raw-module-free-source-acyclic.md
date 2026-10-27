# AlgebraicGeometry.Etale.rawModuleFreeSource_acyclic

## Reason

`coord/retire-items.tsv` explicitly lists the duplicate Sheaf module for retirement.
The upstream theorem has the same universes, hypotheses and conclusion: the old
`RawModuleScalarComparison.forget` is an abbreviation of `moduleAbelianForget`.
A scratch example with the former signature compiles by exactly applying the
upstream theorem. Its axiom audit reports only `propext`, `Classical.choice` and
`Quot.sound`.

There are no current Lean importers of the Sheaf module, including quarantined
sources. Both mathematical parents already import the upstream module. Keep the
node, its proof dependencies, and every parent dependency; reattach its Lean
record to the upstream theorem. The retirement removes the duplicate public
theorem and its two private sections helpers; upstream preserves all three.
No adopted source declaration, signature, attribute or public import is edited.

## Old

The duplicate module's public statement is:

```lean
theorem rawModuleFreeSource_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective I] :
    (preadditiveCoyoneda.obj (op
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawModuleScalarComparison.freeAbelian S U)))).rightAcyclic
      ((RawModuleScalarComparison.forget Λ X).obj I)
```

It publicly imports `Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso`,
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`, and
`Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`, and privately imports all of
`WeilConjectures.AlgebraicGeometry.RawRestrictedHomotopySectionsIso` and
`WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`.
It defines the private helpers `rawSourceSectionsEquiv` and `rawSourceSectionsIso`.

## New

Withdraw the duplicate Sheaf module via `deleted.txt`. The delivery tool writes:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The retained canonical theorem in
`WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceAcyclic` is:

```lean
theorem rawModuleFreeSource_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective I] :
    (preadditiveCoyoneda.obj (op
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawModuleScalarComparison.freeAbelian S U)))).rightAcyclic
      ((moduleAbelianForget Λ X).obj I)
```

The DAG node `lem-sbc-raw-module-free-source-acyclic` keeps its mathematical
statement and proof plan, and records this canonical upstream declaration.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic --uses
AlgebraicGeometry.Etale.rawModuleFreeSource_acyclic` found zero downstream modules;
its sole textual Sheaf declaration occurrence is the retiring module itself.
A search of both library roots and quarantine found no imports of the retired
module. These are the two actual mathematical consumers recorded by the DAG:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic | K4 | Retired duplicate; node points to upstream. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapInjective | unclaimed | Already imports upstream and applies the canonical theorem; no edit. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapSurjective | unclaimed | Already imports upstream and applies the canonical theorem; no edit. |

Their nodes keep `lem-sbc-raw-module-free-source-acyclic` in their proof dependencies.
The unit `sk-lem-failure-field` has no realized attachment to the retired module;
its statement and proof route remain intact. No quarantined parent is withdrawn.

## Status

landed 20261025T051906-L-4186570 2026-10-25 (merge of deliver/K4/Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic)
