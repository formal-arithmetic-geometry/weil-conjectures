# finiteProperBaseChange_of_coefficientIso

## Reason

The private continuous-coefficient helper already proves the canonical projection
formula. State that clause through `moduleObjectProjectionMap` so consumers need
not repeatedly compare its data-record presentation with the expanded adjunction
expression. The item adapter otherwise exceeds the file limit in kernel conversion.
The helper remains private. Every public signature, attribute and import is retained.
Only a proof import is added, and the two existing proofs unfold the small map wrapper.
No mathematical statement or target meaning changes.

## Old

```lean
private theorem finiteProperBaseChange_of_coefficientIso
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar Λ p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
      IsIso ((finiteProperExchange Λ
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
      (M : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso ((((derivedUpperStarLowerStarAdjunction Λ p.left).rightAdjointProjectionMap
        (leftDerivedUpperStarTensor Λ p.left)).app K.obj).app M.obj))
```

## New

```lean
private theorem finiteProperBaseChange_of_coefficientIso
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar Λ p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
      IsIso ((finiteProperExchange Λ
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
      (M : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso (moduleObjectProjectionMap Λ p.left K.obj M.obj))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Private projection interface; public proof unfolds wrapper. |
| Sheaf.Paper.FiniteCoefficientProperFormulaTools | new in this delivery | Applies the private helper through proof-only import all. |
| Sheaf.Paper.IntegralResidueProperFormulas | G3 | Uses the unbundled adapter and private canonical caches. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Public interface unchanged; compile check. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Public interface unchanged; compile check. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Public interface unchanged; compile check. |

## Status

landed 20261026T222655-L-680687 2026-10-26 (merge of deliver/G3/Sheaf.Paper.IntegralResidueProperFormulas)
