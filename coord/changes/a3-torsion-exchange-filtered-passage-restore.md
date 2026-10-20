# AlgebraicGeometry.Etale.isIso_exchange_of_isIso_torsion_pieces

## Reason

Restore the quarantined item listed in coord/rework.tsv. The retired abbreviation
Scheme.PositiveNat in the proof no longer elaborates. Its original body is
PNat.DvdOrder, the index used by fieldInvertibleTorsionDiagram. Expand that alias
in the local proof only. No public interface or target meaning changes.

## Old

The quarantined declaration has this signature:

```lean
theorem identifies
the canonical colimit of the kernels F[n] with F. Each exchange on F[n] is invertible
by the hypothesis. Filtered-colimit exchange makes the exchange on their colimit
invertible; naturality along the canonical comparison isomorphism gives the result.
-/
theorem isIso_exchange_of_isIso_torsion_pieces
    {K : Type u} [Field K] {X S' T : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    [S'.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    (g : T ⟶ S') [g.IsOver (Spec (.of K))]
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F)
    (hpieces : ∀ (n : ℕ) (_hn : n ∈ invertibleTorsionOrders K),
      IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
        (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
          (g := g)).symm)).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (etaleNTorsion F n))))) :
    IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
        (g := g)).symm)).app
      ((DerivedCategory.singleFunctor _ 0).obj F)))
```

Its proof locally declared the index with `fun n : Scheme.PositiveNat ↦ ...`.

## New

The restored declaration has the identical signature:

```lean
theorem identifies
the canonical colimit of the kernels F[n] with F. Each exchange on F[n] is invertible
by the hypothesis. Filtered-colimit exchange makes the exchange on their colimit
invertible; naturality along the canonical comparison isomorphism gives the result.
-/
theorem isIso_exchange_of_isIso_torsion_pieces
    {K : Type u} [Field K] {X S' T : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    [S'.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    (g : T ⟶ S') [g.IsOver (Spec (.of K))]
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F)
    (hpieces : ∀ (n : ℕ) (_hn : n ∈ invertibleTorsionOrders K),
      IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
        (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
          (g := g)).symm)).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (etaleNTorsion F n))))) :
    IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
        (g := g)).symm)).app
      ((DerivedCategory.singleFunctor _ 0).obj F)))
```

The local index now uses `fun n : PNat.DvdOrder ↦ ...`. The parallel-map equality
is proved by rfl. The unused private Coefficients import is removed; public imports
are unchanged. The original two dependency lemmas and naturality argument remain.

## Users

A textual scan of lean/ and quarantine/ finds this one existing consumer. Its call
uses the unchanged theorem signature, and no consumer adaptation is needed.
The item's DAG attachment and dependencies remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Targets.BaseChangeTowardsFields | quarantined | Existing call to the restored theorem unchanged. |

## Status

landed 20261020T162908-L-3673185 2026-10-20 (merge of deliver/A3/Sheaf.AlgebraicGeometry.TorsionExchangeFilteredPassage)
