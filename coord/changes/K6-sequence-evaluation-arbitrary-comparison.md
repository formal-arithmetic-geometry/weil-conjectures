# WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso

## Reason

The original identity-on-section-carriers premise is unnecessary. Its coextension
mate acts pointwise by an invertible map on the finite section carrier. Conjugate
the section bijection of the given comparison on the coextension at level n by
the equivalence evaluating functions on PLift(n ≤ n). The mate at level m applies
that bijection pointwise on PLift(n ≤ m). This is bijective including when n > m,
where the index is empty. Reflecting isomorphisms and taking iterated mates then
gives exactly the existing conclusion. This removes a costly concrete equality-
transport obligation without adding a proof assumption or changing any target.

The dependency module is unclaimed. Its unit sk-rem-sf-pf-done has no realized
statement or proof steps; the existing coextension/iterated-mates route is kept.
The node's statement and Lean signature drop only this premise. The complete
citer audit is in statement_change: both existing citers continue to hold, and
the item newly applies the stronger theorem. No definition or target meaning
changes in this dependency module.

## Old

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
        SheafOfModules.pushforward ψ) :
    IsIso ((mateEquiv adj adjn).symm d.hom).natTrans
```

The private coMate_isIso and coForMate_isIso are generalized in the same way.
The coMate proof now proves pointwise bijectivity rather than identity. All are
fully proved; there are no new declarations, nodes or holes in this module.
All public imports and other declaration signatures remain identical.

## Users

The full transitive import scan via tools/downstream.py --uses identifies only
the following existing textual consumers of this declaration, in addition to its
own declaration. Other importers do not mention it and have unchanged public
interfaces. The item's new proof is also included here.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SequenceModulePullbackEvaluation | unclaimed | Drop unnecessary hd premise; generalize fully proved private mate helpers. |
| Sheaf.Paper.AmbientPullbackTensorCoherence | Y9 | Forced proof adaptation: remove the final identity-on-sections proof argument. All existing signatures and visibility stay identical. |
| Sheaf.Paper.SemilinearOperationsExistence | unclaimed | Applies the stronger theorem; remove only three following all_goals lines which now emit unused/unreachable-tactic warnings. All signatures and other source lines stay unchanged. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | K6 | Fill evaluation existence using the stronger mate theorem, with the actual equality-based comparison. |

Original and adapted consumer compilation results are reported in report.md.

## Status

landed 20261026T023440-L-566781 2026-10-26 (merge of deliver/K6/Sheaf.Paper.CompletedPrimitiveCounitComparison)
