# sequenceModulePullbackEvaluation_isIso

## Reason

The existing docstring and node promise independent site universes, but the Lean declaration used the same object and morphism universes for both sites. Open localization has source Over U in max c v and target C in c. The coextension argument is unchanged and works with independent universes.

## Old

```lean
theorem sequenceModulePullbackEvaluation_isIso
    {D : Type c} [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{r}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (S : Sheaf J RingCat.{r}) (T : Sheaf K RingCat.{r})
    (hA : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A = S)
    (hB : ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{r} K
      (coefficientSequenceTopology K)).obj B = T)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj T)
    (L : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B)
    (Ln : SheafOfModules.{r} S ⥤ SheafOfModules.{r} T)
    (adj : L ⊣ SheafOfModules.pushforward φ)
    (adjn : Ln ⊣ SheafOfModules.pushforward ψ)
    (d : SheafOfModules.pushforward.{r} φ ⋙
        SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hA.symm) ≅
      SheafOfModules.pushforward (F := Prod.sectR n D) (eqToHom hB.symm) ⋙
        SheafOfModules.pushforward ψ)
    (hd : ∀ (N : SheafOfModules.{r} B) (U : C)
        (x : ((SheafOfModules.pushforward φ).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op U) x = x) :
    IsIso ((mateEquiv adj adjn).symm d.hom).natTrans
```

## New

```lean
theorem sequenceModulePullbackEvaluation_isIso
    {D : Type d} [Category.{w} D]
    [UnivLE.{d, r}] [UnivLE.{w, r}] [UnivLE.{max d w, r}]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{r}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (S : Sheaf J RingCat.{r}) (T : Sheaf K RingCat.{r})
    (hA : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A = S)
    (hB : ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{r} K
      (coefficientSequenceTopology K)).obj B = T)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj T)
    (L : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B)
    (Ln : SheafOfModules.{r} S ⥤ SheafOfModules.{r} T)
    (adj : L ⊣ SheafOfModules.pushforward φ)
    (adjn : Ln ⊣ SheafOfModules.pushforward ψ)
    (d : SheafOfModules.pushforward.{r} φ ⋙
        SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hA.symm) ≅
      SheafOfModules.pushforward (F := Prod.sectR n D) (eqToHom hB.symm) ⋙
        SheafOfModules.pushforward ψ)
    (hd : ∀ (N : SheafOfModules.{r} B) (U : C)
        (x : ((SheafOfModules.pushforward φ).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op U) x = x) :
    IsIso ((mateEquiv adj adjn).symm d.hom).natTrans
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SequenceModulePullbackEvaluation | unclaimed | Generalizes the site universes; same proof. |
| Sheaf.Paper.AmbientPullbackTensorCoherence | Y9 | Existing equal-universe application specializes the generalized theorem. |
| Sheaf.Paper.SemilinearOperationsExistence | E7 | Uses the independent-universe case for open localization. |

The downstream scan lists 2850 transitive importers; the declaration-use scan finds only AmbientPullbackTensorCoherence outside the defining module. Public imports and all other public signatures are unchanged.

## Status

landed 20261025T162308-L-404707 2026-10-25 (merge of deliver/E7/Sheaf.Paper.SemilinearOperationsExistence)
