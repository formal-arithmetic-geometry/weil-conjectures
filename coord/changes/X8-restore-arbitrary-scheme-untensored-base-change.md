# AlgebraicGeometry.Etale.arbitraryScheme_untensored_baseChange

## Reason

Restore the complete quarantined module named in `coord/rework.tsv`, keeping its
archived signature, proof, and dependencies. The live file is absent. This
restores a needed theorem; the archive and its DAG attachment remain intact.
There are zero holes in the archive and zero in this restoration. No definition
or target statement changes.

## Old

The live module is absent. The quarantine archive has the following theorem:

```lean
theorem arbitraryScheme_untensored_baseChange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}}
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso ((derivedBaseChangeMapPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (CommSq.mk (pullback.condition
        (f := pullback.snd z (S' ↘ Spec (.of K))) (g := g)).symm)).app
      ((_root_.DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) 0).obj F))
```

## New

The restored module has the same theorem and its complete archived proof:

```lean
theorem arbitraryScheme_untensored_baseChange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}}
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso ((derivedBaseChangeMapPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (CommSq.mk (pullback.condition
        (f := pullback.snd z (S' ↘ Spec (.of K))) (g := g)).symm)).app
      ((_root_.DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) 0).obj F))
```

## Users

`tools/downstream.py` with `--allow-missing --uses` finds zero live downstream
modules. A source and DAG scan also checks quarantined consumers:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | no current claim file found | Quarantined direct importer; restored API is identical to its archived dependency. No adaptation. |

The parent node `lem-kun-0f1j` still cites this theorem's node in its proof and
proof dependencies. The unit route and all DAG dependencies stay intact. No
consumer source file is changed.

## Status

landed 20261021T151212-L-1179251 2026-10-21 (merge of deliver/X8/Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange)
