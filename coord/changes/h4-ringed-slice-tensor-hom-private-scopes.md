# SheafOfModules.ringedSlice_extension_tensor_hom_data private proof scopes

## Reason

Complete the original proof without changing any public signature or definition.
The conservative preflight interface check flags new scope commands (`variable`,
`open`, local notation and options) even though they serve only private helpers.
This record documents those commands and all downstream consumers.

The existing definitions `SheafOfModules.ringedSliceTensorLeft` and
`SheafOfModules.ringedSliceTensorRight` are verbatim unchanged, including bodies.
The public imports are unchanged. The theorem signature below is verbatim identical
in both versions. Only its proof and its proof-only imports change.

## Old

```lean
theorem ringedSlice_extension_tensor_hom_data
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    let S := SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)
    let T := SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U)
    ∃ e : ∀ X : T × S, ∀ H : S,
      (((ringedSliceTensorLeft J R U).obj X ⟶ H) ≃
        ((ringedSliceTensorRight J R U).obj X ⟶ H)),
      (∀ (X : T × S) (H K : S)
          (φ : (ringedSliceTensorLeft J R U).obj X ⟶ H) (h : H ⟶ K),
        e X K (φ ≫ h) = e X H φ ≫ h) ∧
      (∀ (X Y : T × S) (H : S) (f : X ⟶ Y)
          (φ : (ringedSliceTensorLeft J R U).obj Y ⟶ H),
        e X H ((ringedSliceTensorLeft J R U).map f ≫ φ) =
          (ringedSliceTensorRight J R U).map f ≫ e Y H φ)
```

The file has no `SheafOfModules.RingedSliceTensor` helper namespace.

## New

```lean
theorem ringedSlice_extension_tensor_hom_data
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    let S := SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)
    let T := SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U)
    ∃ e : ∀ X : T × S, ∀ H : S,
      (((ringedSliceTensorLeft J R U).obj X ⟶ H) ≃
        ((ringedSliceTensorRight J R U).obj X ⟶ H)),
      (∀ (X : T × S) (H K : S)
          (φ : (ringedSliceTensorLeft J R U).obj X ⟶ H) (h : H ⟶ K),
        e X K (φ ≫ h) = e X H φ ≫ h) ∧
      (∀ (X Y : T × S) (H : S) (f : X ⟶ Y)
          (φ : (ringedSliceTensorLeft J R U).obj Y ⟶ H),
        e X H ((ringedSliceTensorLeft J R U).map f ≫ φ) =
          (ringedSliceTensorRight J R U).map f ≫ e Y H φ)
```

The new helper namespace `SheafOfModules.RingedSliceTensor` contains only explicitly
private declarations. Its `HomData`, `RawTensor` and `SheafifyTensor` sections scope
the additional universe variables, categorical and coefficient variables, the
`open Opposite MonoidalCategory` commands, and the local coefficient notation `A`.
The `backward.isDefEq.respectTransparency` options are confined to these sections
or individual private declarations. The two `backward.defeqAttrib.useBackward`
options are confined to individual private declarations. `open Classical in` is
also confined to individual private declarations. All these scopes end before
the existing public theorem. There are no new instances or attributes on existing public declarations.
The new irreducible implementations and their APIs are private.

No public statement gains or loses a hypothesis. No definition used by a target
changes. No consumer needs adaptation, and the target statement review stays valid.

## Users

The table is the complete downstream list from `tools/downstream.py` on this module,
with holders read from the current claims. Searching each of the three public names
finds only `Sheaf.CategoryTheory.RingedSliceExtensionTensor` outside the item itself.
That consumer applies the unchanged theorem and the two unchanged functors; it does
not access the new helpers or depend on any newly scoped notation or instance.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData | H4 | Proof completed; public interface identical. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion | unclaimed | Indirect consumer; no interface change or adaptation. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat | unclaimed | Indirect consumer; no interface change or adaptation. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits | S4 | Indirect consumer; no interface change or adaptation. |
| Sheaf.CategoryTheory.RingedKoszulCompletionReflector | unclaimed | Indirect consumer; no interface change or adaptation. |
| Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal | H3 | Indirect consumer; no interface change or adaptation. |
| Sheaf.CategoryTheory.RingedSliceExtensionTensor | unclaimed | Uses the three unchanged public declarations; no adaptation. |
| Sheaf.Paper.ExtendedCechCompletionModel | K3 | Indirect consumer; no interface change or adaptation. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | G2 | Indirect consumer; no interface change or adaptation. |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | M1 | Indirect consumer; no interface change or adaptation. |
| Sheaf.Paper.LocallyConstantTensor | N1 | Indirect consumer; no interface change or adaptation. |
| Sheaf.Paper.NilpotentReductionLissity | N2 | Indirect consumer; no interface change or adaptation. |
| Sheaf.Paper.RestrictionLocalCompleteness | A2 | Indirect consumer; no interface change or adaptation. |
| Sheaf.Paper.RingedLocalizationRHomCalculus | P1 | Indirect consumer; no interface change or adaptation. |

## Status

landed 20261018T071157-L-1669729 2026-10-18 (merge of deliver/H4/Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData)
