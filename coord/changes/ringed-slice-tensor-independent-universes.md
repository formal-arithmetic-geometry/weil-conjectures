# SheafOfModules.ringedSlice_extension_tensor

## Reason

The assigned K-flat restriction theorem has independent site object, site morphism,
and coefficient universes. The existing projection formula requires the site morphism
universe to equal the coefficient universe. Generalize the same proved construction:
`C : Type uC`, `Category.{v} C`, and coefficients/modules in `max u v`.
The extra `u` permits every coefficient universe at least as large as `v`.
The direct sums still have precisely the same summands, indexed by arrows to `U`.
No object, map, or tensor product changes in an old specialization (`u = v`).
Both support modules are unclaimed. The assigned theorem's signature is unchanged.
The mathematical node statements already concern arbitrary ringed sites; only
their Lean attachments need the corrected universe generality.

## Old

```lean
theorem ringedSlice_extension_tensor_hom_data
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    let S := SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)
    let T := SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U)
    ∃ e : ∀ X : T × S, ∀ H : S,
      (((ringedSliceTensorLeft J R U).obj X ⟶ H) ≃
        ((ringedSliceTensorRight J R U).obj X ⟶ H)),
      (∀ (X : T × S) (H K : S)
          (φ : (ringedSliceTensorLeft J R U).obj X ⟶ H) (h : H ⟶ K),
        e X K (φ ≫ h) = e X H φ ≫ h) ∧
      (∀ (X Y : T × S) (H : S) (f : X ⟶ Y)
          (φ : (ringedSliceTensorLeft J R U).obj Y ⟶ H),
        e X H ((ringedSliceTensorLeft J R U).map f ≫ φ) =
          (ringedSliceTensorRight J R U).map f ≫ e Y H φ)

theorem ringedSlice_extension_tensor
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    Nonempty (
      ((forget.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)).prod
          (overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙ forget.{u}
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⋙
        MonoidalCategory.tensor
          (C := PresheafOfModules.{u} ((R.over U).obj ⋙ forget₂ CommRingCat RingCat)) ⋙
        PresheafOfModules.sheafification (J := J.over U)
          (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U) (𝟙 _) ⋙
        extensionByZeroPresheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
        PresheafOfModules.sheafification (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          R).obj)) ≅
      (((extensionByZeroPresheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
          PresheafOfModules.sheafification (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          R).obj) ⋙
          forget.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).prod (forget.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ⋙
        MonoidalCategory.tensor (C := PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj R).obj) ⋙
        PresheafOfModules.sheafification (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          R).obj)))
```

```lean
noncomputable def ringedSliceTensorLeft
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    (SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U) ×
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)) ⥤
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)

noncomputable def ringedSliceTensorRight
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    (SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U) ×
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)) ⥤
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)
```

## New

```lean
theorem ringedSlice_extension_tensor_hom_data
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    let S := SheafOfModules.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
    let T := SheafOfModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U)
    ∃ e : ∀ X : T × S, ∀ H : S,
      (((ringedSliceTensorLeft.{uC, u, v} J R U).obj X ⟶ H) ≃
        ((ringedSliceTensorRight.{uC, u, v} J R U).obj X ⟶ H)),
      (∀ (X : T × S) (H K : S)
          (φ : (ringedSliceTensorLeft.{uC, u, v} J R U).obj X ⟶ H) (h : H ⟶ K),
        e X K (φ ≫ h) = e X H φ ≫ h) ∧
      (∀ (X Y : T × S) (H : S) (f : X ⟶ Y)
          (φ : (ringedSliceTensorLeft.{uC, u, v} J R U).obj Y ⟶ H),
        e X H ((ringedSliceTensorLeft.{uC, u, v} J R U).map f ≫ φ) =
          (ringedSliceTensorRight.{uC, u, v} J R U).map f ≫ e Y H φ)

theorem ringedSlice_extension_tensor
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    Nonempty (
      ((forget.{max u v} (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U)).prod
          (overFunctor.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U ⋙ forget.{max u v}
          (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U)) ⋙
        MonoidalCategory.tensor
          (C := PresheafOfModules.{max u v} ((R.over U).obj ⋙ forget₂ CommRingCat.{max u v} RingCat.{max u v})) ⋙
        PresheafOfModules.sheafification.{max u v} (J := J.over U)
          (R := ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U) (𝟙 _) ⋙
        extensionByZeroPresheaf.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U ⋙
        PresheafOfModules.sheafification.{max u v} (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
          R).obj)) ≅
      (((extensionByZeroPresheaf.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U ⋙
          PresheafOfModules.sheafification.{max u v} (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
          R).obj) ⋙
          forget.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)).prod (forget.{max u v}
          ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))) ⋙
        MonoidalCategory.tensor (C := PresheafOfModules.{max u v} ((sheafCompose J (forget₂ CommRingCat.{max u v}
          RingCat.{max u v})).obj R).obj) ⋙
        PresheafOfModules.sheafification.{max u v} (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
          R).obj)))
```

```lean
noncomputable def ringedSliceTensorLeft
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    (SheafOfModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U) ×
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

noncomputable def ringedSliceTensorRight
    {C : Type uC} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    (SheafOfModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U) ×
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
```

The public functor definitions have the same functor bodies, with
coefficient/module universe `max u v`. Private helpers use
explicit universe arguments to avoid ambiguous inference through `max`.
The private Yoneda argument now allows arbitrary independent object and morphism
universes in its two categories. All constructions and proofs remain complete.
No target statement or definition of a target changes its mathematical meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits | unclaimed | Direct consumer: old universe specialization; no edit required. |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat | E8 | New proof uses generalized projection formula; statement unchanged. |
| Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence | Q1 | Transitive consumer; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeArrowLocalization | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | A2 | Transitive consumer; statements and definitions unchanged. |
| Sheaf.CategoryTheory.RingedAugmentedCechRestriction | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence | M9 | Transitive consumer; statements and definitions unchanged. |
| Sheaf.CategoryTheory.RingedLocalizationFactorRestriction | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.CategoryTheory.RingedSliceExtensionTensor | unclaimed | Generalized interface and complete proof; old specialization unchanged. |
| Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData | unclaimed | Generalized interface and complete proof; old specialization unchanged. |
| Sheaf.Paper.FiniteCoefficientTensorCtf | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.FinitePerfectQuotientModels | W6 | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.LocallyConstantTensor | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.NilpotentReductionLissity | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.NilpotentReductionStep | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.NormalizedTowerCommonLisseStrata | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedDerivedSliceLocalization | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedLocalizationCurrying | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedLocalizationModels | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedLocalizationRHomCalculus | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedLocalizationRestriction | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedModelCurrying | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedModelCurryingCoherence | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedModelRestriction | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedSliceDerivedComparisons | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.RingedSliceDerivedMate | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SiteTensorLocalModelComparison | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionData | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation | unclaimed | Transitive consumer; statements and definitions unchanged. |
| Sheaf.SixFunctors.ComparisonOpenTensorCoherence | U6 | Transitive consumer; statements and definitions unchanged. |
| Sheaf.SixFunctors.OpenTensorNormalization | U8 | Transitive consumer; statements and definitions unchanged. |

## Status

landed 20261020T144246-L-2259197 2026-10-20 (merge of deliver/E8/Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat)
