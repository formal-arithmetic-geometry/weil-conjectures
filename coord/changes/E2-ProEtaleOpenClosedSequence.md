# AlgebraicGeometry.ProEtale.exact_openClosedSequence

## Reason

The DAG attaches this declaration to `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence`,
but that source module is absent in the shared checkout. Its attachment also names
`Scheme.proEtaleSheafAdjunction`, which the current API does not define. Restore the module
and prove its statement using `ProEtale.upperStarLowerStarAdjunction`, the actual adjunction
already used throughout the library. This changes no existing Lean declaration: no source file
or consumers exist for the recorded attachment. The mathematical statement, coefficient ring,
immersions, quasi-compactness hypothesis, and the actual unit and counit arrows stay the same.
No target definition or target statement changes.

Repair of the returned delivery: the first version copied seven coefficient-independent private
lemmas already stated in `ProEtaleAbelianClosedCounit`. The repaired sequence module instead
imports the existing public module-valued closed-immersion API. All seven duplicates, their
private base-change definition, and the now-unneeded affine and detection helpers are removed.
The mathematical sequence and both arrows are identical.

## Old

The absent module's recorded Lean signature was:

```lean
theorem exact_openClosedSequence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ) (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Mono ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F) ∧ Epi ((Scheme.proEtaleSheafAdjunction i (ModuleCat.{u + 1} Λ)).unit.app F) ∧ (ComposableArrows.mk₂ ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F) ((Scheme.proEtaleSheafAdjunction i (ModuleCat.{u + 1} Λ)).unit.app F)).Exact
```

## New

```lean
theorem exact_openClosedSequence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F) ∧
      Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F) ∧
      (ComposableArrows.mk₂
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F)
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F)).Exact
```

## Users

`tools/downstream.py` reports the module unknown, consistently with the absent source file.
A repository-wide `rg` search finds no import of the module or use of the declaration.
The only consumer introduced by this delivery is listed below. The existing public module-valued results in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` are imported and reused.
That module and the abelian source modules remain unchanged. The repair deletes the copied
private counit/mate route and the local copies of detection and disjoint-support arguments;
no existing declaration changes visibility or signature.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence | unclaimed; absent source | Restore and prove the recorded interface using the current adjunction name. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | E2; new | Use the actual unit/counit short exact sequence to glue classicality. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | E2 | Proof imports only; all existing signatures, definitions and public imports unchanged. |

## Status

landed 20261016T115357-L-2682075 2026-10-16 (merge of deliver/E2/WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf)
