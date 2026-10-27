# source, tensorTarget, strictTensor

## Reason

Repeated conversion of product-functor records to fixed-factor curried tensor records
caused expensive definitional equality checks and 60-second compile failures. Express
the same functors as compositions with their fixed-factor tensor functor. Objects and
maps are the same canonical tensor objects and maps, with the same coefficient-first
order. Public signatures, the actual projection map, and all theorem statements stay
unchanged. These are Sheaf definitions, with no source-library edit.

## Old

```lean
def source : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  ((DerivedCategory.singleFunctor _ 0).prod'
    ((Functor.const _).obj ((proEtaleRingDerivedDirectImage f R S c).obj C))) ⋙ a.tensor

def tensorTarget : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules X S) :=
  ((DerivedCategory.singleFunctor _ 0 ⋙ proEtaleRingDerivedPullback f R S c).prod'
    ((Functor.const _).obj C)) ⋙ b.tensor

def strictTensor (K : CochainComplex (proEtaleRingModules X S) ℤ) :
    proEtaleRingModules Y R ⥤ CochainComplex (proEtaleRingModules X S) ℤ :=
  ((proEtaleRingModulePullback f R S c ⋙ CochainComplex.singleFunctor _ 0).prod'
    ((Functor.const _).obj K)) ⋙ Functor.uncurry.obj
      ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
```

## New

```lean
def source : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  DerivedCategory.singleFunctor _ 0 ⋙ (Functor.curryObj a.tensor).flip.obj
    ((proEtaleRingDerivedDirectImage f R S c).obj C)

def tensorTarget : proEtaleRingModules Y R ⥤ DerivedCategory (proEtaleRingModules X S) :=
  DerivedCategory.singleFunctor _ 0 ⋙ proEtaleRingDerivedPullback f R S c ⋙
    (Functor.curryObj b.tensor).flip.obj C

def strictTensor (K : CochainComplex (proEtaleRingModules X S) ℤ) :
    proEtaleRingModules Y R ⥤ CochainComplex (proEtaleRingModules X S) ℤ :=
  proEtaleRingModulePullback f R S c ⋙ CochainComplex.singleFunctor _ 0 ⋙
    ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj K
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FilteredFiniteFreeProjection | U7 | Proofs use the explicit composite functors and their preservation/additivity instances. |

`tools/downstream.py` reports zero downstream modules and only this module as a
user of each of the three names. No consumer requires adaptation. The definitions
continue to denote the same ordinary uncompleted derived and strict tensor functors;
no target meaning changes.

## Status

landed 20261024T020757-L-2664823 2026-10-24 (merge of deliver/U7/Sheaf.AlgebraicGeometry.FilteredFiniteFreeProjection)
