# AlgebraicGeometry.Etale.closedConstantDerivedPairMap

## Reason

Construct the same tensor bifunctor map through the generic derivedTensorPairMap API. Profiling the original composite in the expanded proof module showed 6.66 seconds of kernel checking. Both definitions use the identical first-variable map followed by the identical second-variable map; this only checks the composite before specializing coefficients. No target signature changes. Definitions used by targets retain the same mathematical meaning; their canonical constructions can be read directly in the new helper bodies. The semantic review should verify these definitional identities.

## Old

```lean
noncomputable def closedConstantDerivedPairMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  ((derivedTensor B X).map f).app L ≫ ((derivedTensor B X).obj K').map g
```

## New

```lean
noncomputable def closedConstantDerivedPairMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  derivedTensorPairMap X f g
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor | U4 | Same object or arrow, with its canonical generic API; proof adapted here. |

`tools/downstream.py --uses closedConstantDerivedPairMap` finds no other direct user. The three transitive consumers are Sheaf.Paper.SupportedCup, Sheaf.Paper.PurityFrameClass and Sheaf.Paper.PurityFramePrincipalBoundary. Their original statements and proofs require no edits; they compile unchanged against the delivered definitions (SupportedCup 17.6 s, PurityFramePrincipalBoundary 23.7 s, PurityFrameClass 13.9 s). No source-library declaration is changed.

## Status

landed 20261020T233227-L-908718 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor)
