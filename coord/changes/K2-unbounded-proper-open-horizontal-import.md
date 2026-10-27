# AlgebraicGeometry.Etale.etaleProperOpenHorizontalNormalization

## Reason

Remove an unnecessary private dependency on `UnboundedProperOpenComposition` so
that the existing proved arbitrary-scheme theorem can be reused to close its
Noetherian predecessor. The removed import was used only for `open_compare_mono`.
Copy that proved private helper next to its use and import its actual dependency.
This unclaimed Sheaf module keeps every existing declaration, signature, visibility,
attribute, definition and public import verbatim. Its mathematical proof route is
unchanged, so its DAG node needs no edit.

## Old

```lean
import all Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition
```

The imported private `open_compare_mono` is the proof now included below, verbatim.

## New

```lean
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition

private theorem open_compare_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (k : X ⟶ Y) [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) := by
  obtain ⟨L, ι, hi, _, ho, _⟩ := properSupportSheafComposition Λ
  have hι : Mono ((ι k).app F) := by
    refine ⟨fun {Z} a b hab ↦ ?_⟩
    ext V s
    apply (hi X Y k F V.unop).1
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun z ↦ z.hom) hab) V) s
  obtain ⟨o, he⟩ := ho X Y k
  have he' := congr_app he F
  dsimp only [NatTrans.comp_app] at he'
  rw [← he']
  infer_instance
```

## Users

The table includes all direct importers, the textual users of the public theorem
reported by `tools/downstream.py --uses`, and the new user in this delivery.
There is no interface change; no downstream source adaptation is required.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization` | unclaimed | Public and existing private declarations unchanged; no consumer adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleProperOpenCartesianNormalization` | unclaimed | Public and existing private declarations unchanged; no consumer adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleProperOpenExchangeCube` | unclaimed | Public and existing private declarations unchanged; no consumer adaptation. |
| `Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting` | unclaimed | Public and existing private declarations unchanged; no consumer adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleProperOpenCubeNormalization` | unclaimed | Public and existing private declarations unchanged; no consumer adaptation. |
| `Sheaf.AlgebraicGeometry.UnboundedProperOpenHorizontalComposition` | K2 | Can import and specialize the proved theorem after the private import cycle is removed. |

## Status

landed 20261026T222728-L-687235 2026-10-26 (merge of deliver/K2/Sheaf.AlgebraicGeometry.UnboundedProperOpenHorizontalComposition)
