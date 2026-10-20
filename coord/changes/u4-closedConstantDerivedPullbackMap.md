# AlgebraicGeometry.Etale.closedConstantDerivedPullbackMap

## Reason

Construct the same composite through the generic singleFunctorPullbackMap API before specializing coefficients to ModuleCat A. Profiling the concrete composite showed 6.43 seconds of kernel checking. The helper still uses exactly singleFunctorCompLeftDerivedUpperStarIso.hom followed by singleFunctor.map of the specified ordinary arrow. No target signature changes. Definitions used by targets retain the same mathematical meaning; their canonical constructions can be read directly in the new helper bodies. The semantic review should verify these definitional identities.

## Old

```lean
noncomputable def closedConstantDerivedPullbackMap (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor).obj
      ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj
          (closedConstantModule A (pullback.fst v i)) :=
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map (closedConstantPullbackAdjoint A i v)
```

## New

```lean
noncomputable def closedConstantDerivedPullbackMap (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor).obj
      ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj
          (closedConstantModule A (pullback.fst v i)) :=
  singleFunctorPullbackMap v (closedConstantPullbackAdjoint A i v)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor | U4 | Same object or arrow, with its canonical generic API; proof adapted here. |

`tools/downstream.py --uses closedConstantDerivedPullbackMap` finds no other direct user. The three transitive consumers are Sheaf.Paper.SupportedCup, Sheaf.Paper.PurityFrameClass and Sheaf.Paper.PurityFramePrincipalBoundary. Their original statements and proofs require no edits; they compile unchanged against the delivered definitions (SupportedCup 17.6 s, PurityFramePrincipalBoundary 23.7 s, PurityFrameClass 13.9 s). No source-library declaration is changed.

## Status

landed 20261020T233227-L-908718 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor)
