# WeilConjectures.FrobeniusCoefficientTwists.augmentationComplexComparison

## Reason

The handwritten termwise natural transformation repeatedly unfolds the module
pullback and its adjunction during type checking. Use Mathlib's mapped natural
isomorphism. Its component in degree i is the same adjunction comparison, so the
normalization on module sections and the public augmentation statement are unchanged.
The helper is private and is used only in the assigned module's proofs.

## Old

```lean
private def augmentationComplexComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      IntegralOnSlice.ordinaryComplexPull l E g where
  app P :=
    { f := fun i ↦ (augmentationPullIso l E g).hom.app (P.X i)
      comm' := fun i j _ ↦ ((augmentationPullIso l E g).hom.naturality (P.d i j)).symm }
  naturality _ _ f := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (augmentationPullIso l E g).hom.naturality (f.f i)
```

## New

```lean
private def augmentationComplexComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
      IntegralOnSlice.ordinaryComplexPull l E g := by
  let F₀ : IntegralOnSlice.Mod l E Y none ⥤ IntegralOnSlice.Mod l E X none :=
    modulePull l E g
  let e₀ : F₀ ≅ IntegralOnSlice.ordinaryPull l E g := augmentationPullIso l E g
  let : F₀.Additive := proEtaleRingModulePullback_additive g _ _ _
  let : (IntegralOnSlice.ordinaryPull l E g).Additive := Functor.additive_of_iso e₀
  exact (NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R9 | Uses the generic termwise comparison with identical components; normalization and isomorphism proofs check the same equations. |

The library-wide text search finds no other user of this private helper. No target
statement or public definition is changed; there is no consumer adaptation.

## Status

landed 20261026T070903-L-3686575 2026-10-26 (merge of deliver/R9/Sheaf.Paper.FrobeniusCoefficientTwistsCanonical)
