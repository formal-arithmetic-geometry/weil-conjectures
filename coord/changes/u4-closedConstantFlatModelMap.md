# AlgebraicGeometry.Etale.closedConstantFlatModelMap

## Reason

Give the canonical flat-model pairing an explicit derivedTensor result type and delegate its construction to singleFunctorFlatPairing. The new helper is exactly singleFunctorObjTensorIso.hom followed by singleFunctor.map f. No arrow or flat model changes. The explicit type avoids comparing alternative monoidal instance terms at concrete ModuleCat coefficients. No target signature changes. Definitions used by targets retain the same mathematical meaning; their canonical constructions can be read directly in the new helper bodies. The semantic review should verify these definitional identities.

## Old

```lean
noncomputable def closedConstantFlatModelMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (L F G : Sheaf X.smallEtaleTopology B)
    (h : ObjectProperty.flat L) (f : L ⊗ F ⟶ G) :=
  (singleFunctorObjTensorIso (A := B) (X := X) L F h).hom ≫
    (DerivedCategory.singleFunctor _ 0).map f
```

## New

```lean
noncomputable def closedConstantFlatModelMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (L F G : Sheaf X.smallEtaleTopology B)
    (h : ObjectProperty.flat L) (f : L ⊗ F ⟶ G) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
        (DerivedCategory.singleFunctor _ 0).obj G :=
  singleFunctorFlatPairing L F G h f
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor | U4 | Same object or arrow, with its canonical generic API; proof adapted here. |

`tools/downstream.py --uses closedConstantFlatModelMap` finds no other direct user. The three transitive consumers are Sheaf.Paper.SupportedCup, Sheaf.Paper.PurityFrameClass and Sheaf.Paper.PurityFramePrincipalBoundary. Their original statements and proofs require no edits; they compile unchanged against the delivered definitions (SupportedCup 17.6 s, PurityFramePrincipalBoundary 23.7 s, PurityFrameClass 13.9 s). No source-library declaration is changed.

## Status

landed 20261020T233227-L-908718 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor)
