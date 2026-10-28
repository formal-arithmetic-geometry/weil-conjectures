# AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_model_homology_identification

## Reason
The original interface omitted the isomorphism hypothesis required to identify the chosen derived scalar change with ordinary scalar change on the model. For a non-flat coefficient map and a non-K-flat complex, derived scalar extension can have Tor homology that ordinary tensor homology does not, so the original statement was false. The corrected theorem follows the exact coefficient-transport route and adds `hφ : ∀ n : ℕ, IsIso (φ n)`.

## Old
```lean
theorem finiteQuotient_layer_tensor_model_homology_identification
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ) (q : ℤ) :
    Nonempty
      (((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedAdicDerivedChange X (φ (n + 1))).obj
              (DerivedCategory.Q.obj
                (finiteModelConstantComplex X _
                  (finiteQuotientLayerTensorComplex d.ideal n P)))))) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((finiteCoefficientConstantFunctor X
            (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj
            ((finiteQuotientLayerTensorComplex d.ideal n P).homology q)))
```

## New
```lean
theorem finiteQuotient_layer_tensor_model_homology_identification
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ) (q : ℤ) :
    Nonempty
      (((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedAdicDerivedChange X (φ (n + 1))).obj
              (DerivedCategory.Q.obj
                (finiteModelConstantComplex X _
                  (finiteQuotientLayerTensorComplex d.ideal n P)))))) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((finiteCoefficientConstantFunctor X
            (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj
            ((finiteQuotientLayerTensorComplex d.ideal n P).homology q)))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison | P3 | Forced proof adaptation: pass the existing `hφ` argument to the corrected theorem. |

## Status
landed 20261028T020711-L-2539110 2026-10-28 (merge of deliver/R5/Sheaf.Paper.FiniteQuotientLayerTensorModelHomologyIdentification)
