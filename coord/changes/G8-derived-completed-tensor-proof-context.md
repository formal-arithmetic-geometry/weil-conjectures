# CategoryTheory.DerivedCompletedTensor local proof context

## Reason

The preflight classifies new variable/attribute commands as an interface change and
requires this record. These commands support private, fully proved helpers. No existing
public signature, public import, definition body, or global attribute changes. The three
existing declarations are coefficientLinear, HomAction, and bilinearity; their signatures
are textually identical, and the two data declarations are textually identical in full.
No target meaning changes and no downstream adaptation is required.

## Old

The original contiguous derived-category variable context was:

```lean
variable [HasDerivedCategory.{w} (KoszulSmallModel.Modules R)]
  [HasDerivedCategory.{w₀} (ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))]
  [∀ U : SmallModel.{r} C, HasDerivedCategory.{w₀} (SheafOfModules.{r}
    ((sheafCompose (((equivSmallModel.{r} C).inverse.inducedTopology J).over U)
      (forget₂ CommRingCat.{r} RingCat.{r})).obj ((KoszulSmallModel.ring R).over U)))]

```

There was no ScalarExtension section, local irreducibility attribute, or
backward.isDefEq.respectTransparency option.

## New

The same assumptions are introduced in two commands, with the private
`derivedTensorLinear` proof between them. This prevents irrelevant small-model
instances from participating in its typeclass search:

```lean
variable [HasDerivedCategory.{w} (KoszulSmallModel.Modules R)]


variable [HasDerivedCategory.{w₀} (ringedSiteModules.{r}
    ((sheafCompose _ (forget₂ CommRingCat.{r} RingCat.{r})).obj (KoszulSmallModel.ring R)))]
  [∀ U : SmallModel.{r} C, HasDerivedCategory.{w₀} (SheafOfModules.{r}
    ((sheafCompose (((equivSmallModel.{r} C).inverse.inducedTopology J).over U)
      (forget₂ CommRingCat.{r} RingCat.{r})).obj ((KoszulSmallModel.ring R).over U)))]

```

The new private generic calculation uses the following section, closed before either
existing derived-category variable block:

```lean
section ScalarExtension
variable {D : Type*} [Category* D] [Preadditive D]
  (A : Type*) [CommRing A] [Linear A D] (B : D × D ⥤ D)
  [∀ M, ((Functor.curry.obj B).obj M).Additive]
  [∀ M, ((Functor.curry.obj B).obj M).Linear A]
  [∀ M, ((Functor.curry.obj B).flip.obj M).Additive]
  [∀ M, ((Functor.curry.obj B).flip.obj M).Linear A]

-- fully proved private helpers only
end ScalarExtension
```

The following proof elaboration settings are local to this file. The attribute is
explicitly local and does not alter the imported definitions or their global reducibility:

```lean
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] KoszulSmallModel.complete
  SheafOfModules.siteDerivedTensorIndependentCoefficients
```

## Users

`tools/downstream.py Sheaf.Paper.DerivedCompletedTensorBilinearity --uses bilinearity
coefficientLinear HomAction` reports zero downstream modules and only the item's own
three declarations as textual uses. DAG parents still retain the theorem; none is
withdrawn or changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedCompletedTensorBilinearity | G8 | Private proof helpers and local elaboration context; existing public declarations unchanged. |

## Status

landed 20261021T163758-L-1082250 2026-10-21 (merge of deliver/G8/Sheaf.Paper.DerivedCompletedTensorBilinearity)
