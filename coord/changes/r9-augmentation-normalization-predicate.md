# WeilConjectures.FrobeniusCoefficientTwists.existsUnique_pullbackAugmentation

## Reason

Factor the existing explicit normalization property through the public definition
pullbackAugmentationNormalization. Its body is verbatim the old property's formula.
The binder list, coordinate equations and mathematical statement are unchanged by
definitional equality. This avoids repeatedly comparing the expanded cone and product
coordinates at every use of the unique-existence theorem. No Challenge declaration changes.
The new predicate has a real body and no proof hole.

## Old

```lean
theorem existsUnique_pullbackAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! eta : (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
        integralOperationsPullbackComplexFunctor l E g,
      (∀ (C : CochainComplex (integralTowerModules l E Y) ℤ)
        (i : ℤ) (n : ℕ) (V : Y.ProEt) (x : (C.X i).val.obj (op V)),
        (((eta.app C).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsPullbackTowerFunctor
                l E g).obj C).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsPullbackTowerFunctor
                  l E g).obj C)))).f i ≫
          (Pi.π (fun j ↦ ((integralOperationsPullbackTowerFunctor
            l E g).obj C).obj (op j)) n).f i).val.app
              (op ((proEtaleBaseChange g).obj V)))
          (moduleSection l E g (C.X i) V x) =
            integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj
                C).X i) V
              (unrestrictedIntegralTensorSection l E Y n
                (C.X i) (op V) 1 x)) ∧
      ∀ (C : CochainComplex (integralTowerModules l E Y) ℤ)
        (i : ℤ),
        (eta.app C).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsPullbackTowerFunctor
                l E g).obj C).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsPullbackTowerFunctor
                  l E g).obj C)))).v i (i - 1) (by omega) = 0
```

## New

```lean
theorem existsUnique_pullbackAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! eta : (modulePull l E g).mapHomologicalComplex (.up ℤ) ⟶
        integralOperationsPullbackComplexFunctor l E g,
      pullbackAugmentationNormalization l E g eta
```

## Users

| Module | Current holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R9 | Uses the same normalization predicate in construction, uniqueness and choice normalization. |
| Sheaf.Paper.IntegralPullbackAugmentationAmbient | unclaimed | Its pair of coordinate equations unfolds the same predicate; no source edit is needed. |

A full source search finds only the external consumer listed above. All inferred proof arguments
and data constructions are definitionally the same. No consumer source is adapted.

## Status

landed 20261026T070903-L-3686575 2026-10-26 (merge of deliver/R9/Sheaf.Paper.FrobeniusCoefficientTwistsCanonical)
