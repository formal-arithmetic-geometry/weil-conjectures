# exact_openClosedSequence

## Reason

The assigned classicality theorem allows infinite Noetherian coefficient rings.
This support theorem unnecessarily required finite coefficients. Its existing argument
works for arbitrary commutative rings. No definition or target statement changes.
The modified support module is unclaimed. No adaptation of another held module is made.

## Old

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

## New

```lean
theorem exact_openClosedSequence (Λ : Type (u + 1)) [CommRing Λ]
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

The table lists direct declaration users from
`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence --uses exact_openClosedSequence`.
Every downstream statement stays identical. Direct consumers keep their proofs;
the changed theorem is strictly more general and retains their specializations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical | Q6 | Statement unchanged; removing a hypothesis preserves its finite-ring use. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence | unclaimed | Generalized here; proof retained. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | Statement unchanged; removing a hypothesis preserves its finite-ring use. |

## Status

landed 20261019T005405-L-2762980 2026-10-19 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical)
