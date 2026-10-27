# p1KummerDerivedInsertion

## Reason

Concrete composition and Ext proofs repeatedly unfold the raw single-functor adjunction
transpose, making their kernel checks exceed the 60-second file limit. Factor precisely
that formula through a generic exact-functor adjoint-insertion definition, with proved
composition and invertibility API. No coefficient object, adjunction, ordinary
insertion or normalization changes.

The adapted module Sheaf.Paper.P1KummerScalarEndpoints is unclaimed. Its existing public
signatures and visibility are preserved. The new public import supplies the public definition
body's generic construction.

## Old

```lean
def p1KummerDerivedInsertion {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj G :=
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).symm
    ((_root_.DerivedCategory.singleFunctor _ 0).map η ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app G)
```

## New

```lean
def p1KummerDerivedInsertion {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj G :=
  SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η
```

The new body unfolds to the old expression, with the identical exact right adjoint and
single-functor comparison. Targets have the identical elaborated types and mathematical
meaning; no target-definition interpretation changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.P1KummerScalarEndpoints | unclaimed | Definition body factored; signature preserved. |
| Sheaf.Paper.P1KummerDerivedScalar | U1 | Uses the same record and proves its existing theorem. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | No use of the insertion definition; no adaptation. |

`tools/downstream.py Sheaf.Paper.P1KummerScalarEndpoints --uses p1KummerDerivedInsertion`
reports the two downstream modules above and insertion uses only in the endpoint module.

The unchanged VectorTraceScalarDescent consumer compiled in 40.1 seconds during this
session and passed the final retained-packet consumer check in 41.1 seconds. No consumer
signature or proof is adapted.

## Status

landed 20261024T191330-L-308566 2026-10-24 (merge of deliver/U1/Sheaf.Paper.P1KummerDerivedScalar)
