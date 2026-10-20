# AlgebraicGeometry.Etale.tensorProjectionAdjunct

## Reason

The delivery's private proof calculations need controlled instance inference to avoid
expanding alternate sheaf tensor structures. The static interface checker records added
attribute commands as an interface change, even when they are local. Each attribute is
now scoped to its single declaration with `in`; no instance registration or removal is
exported. This record documents the conservative interface diagnostic. No definition,
existing public signature, target meaning or canonical map changes.

## Old

The theorem has the following signature and no surrounding attribute commands:

```lean
theorem tensorProjectionAdjunct
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategoryModule Λ Y) (E : DerivedCategoryModule Λ X)
    (a : M ⟶ (R((f)_*[ModuleCat.{u + 1} Λ])).obj E) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj M)
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj E)).symm
      (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).map a ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app K).app
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K ≫
        (R((f)_*[ModuleCat.{u + 1} Λ])).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app E).app
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) f).app K).app M ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).map
          ((L((f)^*[ModuleCat.{u + 1} Λ])).map a ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app E)
```

## New

The same signature, preceded by declaration-local proof elaboration settings:

```lean
attribute [local instance high] SymmetricCategory.toBraidedCategory in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
theorem tensorProjectionAdjunct
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategoryModule Λ Y) (E : DerivedCategoryModule Λ X)
    (a : M ⟶ (R((f)_*[ModuleCat.{u + 1} Λ])).obj E) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj M)
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj E)).symm
      (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).map a ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app K).app
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K ≫
        (R((f)_*[ModuleCat.{u + 1} Λ])).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app E).app
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) f).app K).app M ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).map
          ((L((f)^*[ModuleCat.{u + 1} Λ])).map a ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app E)
```

The two new private calculation lemmas have the same declaration-local settings.
The new cancellation module likewise scopes its negative instance attributes to each
individual theorem. Its `swapInvolutive` predicate is a real explicit definition, used
only in private proven theorems. It is absent from every public signature.

## Users

`tools/downstream.py Sheaf.SixFunctors.TensorProjectionAdjunct --uses
tensorProjectionAdjunct` reports no external textual use of the declaration and 798
transitive importers. Their statements and proofs keep the identical public theorem
and identical exported instance environment: declaration-local `in` commands are
restored when each declaration ends. No consumer is edited or requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.TensorProjectionAdjunct | X3 | One original hole proved; unchanged signature |

The new helper module has only this item's private proof import as a consumer in
this packet. There are no forced adaptations of modules held by other groups.

## Status

landed 20261020T131233-L-1264467 2026-10-20 (merge of deliver/X3/Sheaf.SixFunctors.TensorProjectionAdjunct)
