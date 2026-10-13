# exists_higher_image_raw_affine_image_rep

## Reason

The expanded raw-to-sheaf signature triggers expensive kernel conversion of the
associated sheaf and its underlying abelian presheaf, even with a `sorry` body.
The original expanded proof and its explicit-endpoint variant exceed the fixed
60-second limit. Use the existing `higherDirectImageRawOverPresheaf` and
`higherDirectImageRawOverComparison` abbreviations in this intermediate theorem.
They expand to exactly the previously displayed raw presheaves and canonical
comparison maps. Every binder, universe, hypothesis, witness and equality is
preserved. There is no new definition or mathematical statement, and no target
statement or definition used by a target changes.

The raw-over naturality module is now imported publicly because its existing
abbreviations occur in the public signature. All previous public imports remain.
The colimit argument stays in the item's file; the previous attempted core split
is removed. No timeout is avoided by splitting the proof into files.

## Old

```lean
theorem exists_higher_image_raw_affine_image_rep
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left]
    (z : (higherDirectImagePresheaf Λ (c.pt.hom ≫ k) q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))).obj (op U)) :
    ∃ (i : I)
      (t : (higherDirectImagePresheaf Λ ((D.obj i).hom ≫ k) q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).obj (op U)),
      ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op U))
        ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app (op U) t) =
      (higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app (op U) z
```

## New

```lean
theorem exists_higher_image_raw_affine_image_rep
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left]
    (z : (higherDirectImageRawOverPresheaf Λ k G q c.pt).obj (op U)) :
    ∃ (i : I)
      (t : (higherDirectImageRawOverPresheaf Λ k G q (D.obj i)).obj (op U)),
      ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op U))
        ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app (op U) t) =
      (higherDirectImageRawOverComparison Λ k G q c.pt).app (op U) z
```

## Users

The source-only downstream scan reports 135 modules, all listed below with
the local claim snapshot. Only HigherDirectImageColimitComparisonEpi directly calls
the theorem. The proposition and all previous public exports are preserved;
The sole direct caller needs the one forced proof adaptation below. No other
downstream source is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | Y3 | Same proposition via existing abbreviations; proof closed. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Forced proof adaptation: use the same comparison abbreviation in τ and he. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| TargetsCheck | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Definitionally equal statement and retained public exports; no adaptation. |

The original `Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi`
(holder: unclaimed) compiles against the published baseline, but fails against
the compiled changed item. The exact counterfactual compiler diagnostic is:

```text
/home/ubuntu/weil-sandbox/Y3/Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep/scratchpad/user-test/lean/Sheaf/AlgebraicGeometry/HigherDirectImageColimitComparisonEpi.lean:124:4: error: Type mismatch: After simplification, term
  he
 has type
  (ConcreteCategory.hom (a'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        ((ConcreteCategory.hom
            ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
                  ((DerivedCategory.Plus.singleFunctor (Sheaf (D.obj i).left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                    (((D.obj i).hom)^*[ModuleCat Λ].obj G))).app
              (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
          t)) =
    (ConcreteCategory.hom (b'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        ((ConcreteCategory.hom
            ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
                  ((DerivedCategory.Plus.singleFunctor (Sheaf (D.obj i).left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                    (((D.obj i).hom)^*[ModuleCat Λ].obj G))).app
              (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
          t))
but is expected to have type
  (ConcreteCategory.hom (a'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
                ((DerivedCategory.Plus.singleFunctor (Sheaf c.pt.left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                  ((c.pt.hom)^*[ModuleCat Λ].obj G))).app
            (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        z) =
    (ConcreteCategory.hom (b'.hom.app (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
      ((ConcreteCategory.hom
          ((higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
                ((DerivedCategory.Plus.singleFunctor (Sheaf c.pt.left.smallEtaleTopology (ModuleCat Λ)) 0).obj
                  ((c.pt.hom)^*[ModuleCat Λ].obj G))).app
            (op ((Scheme.AffineEtale.Spec S).obj (unop U)))))
        z)

(with the modules compiled into /home/ubuntu/weil-sandbox/Y3/Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep/scratchpad/user-test/.lbuild) [47.3 s]
[exit code 1: NOT compiled]

```

The old final simp list cannot rewrite the returned representative equality:
its left side uses the comparison abbreviation while `he` evaluates the
expanded canonical map. The forced adaptation uses the same existing
abbreviation for the local limit comparison `τ`, for the stage evaluation in
`he`, and for the displayed shape of `he`. The final simp step is unchanged.
Changing just the stage evaluation still produces an implicit-type mismatch
between the expanded limit comparison and `τ`; keeping the limit comparison
in the same abbreviated form removes that conversion too.

The adapted module compiles against the delivered item. No import, helper,
declaration, signature or visibility changes in it. These are all changed lines:

```diff
--- original

+++ adapted

@@ -81,9 +81,7 @@

     (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
   let A := sheafCompose S.smallEtaleTopology
     (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
-  let τ := higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
-    ((DerivedCategory.Plus.singleFunctor _ 0).obj
-      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))
+  let τ := higherDirectImageRawOverComparison Λ k G q c.pt
   have hτ : Presheaf.IsLocallySurjective S.smallEtaleTopology τ :=
     (isLocallyBijective_higherDirectImagePresheafToSheaf Λ _ _ _).2
   refine ⟨?_⟩
@@ -108,19 +106,13 @@

       simpa only [hB, Category.assoc, Iso.inv_hom_id_assoc] using h
     have he := congrArg (fun f ↦ (f.hom.app
       (op ((Scheme.AffineEtale.Spec S).obj U.unop)))
-        ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
-          ((DerivedCategory.Plus.singleFunctor _ 0).obj
-            ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app
-              (op ((Scheme.AffineEtale.Spec S).obj U.unop)) t)) hi
+        ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app
+          (op ((Scheme.AffineEtale.Spec S).obj U.unop)) t)) hi
     change (a'.hom.app _) (τ.app _ z) = (b'.hom.app _) (τ.app _ z)
     change (a'.hom.app _) (((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app _)
-      ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
-        ((DerivedCategory.Plus.singleFunctor _ 0).obj
-          ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app _ t)) =
+      ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app _ t)) =
       (b'.hom.app _) (((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app _)
-        ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
-          ((DerivedCategory.Plus.singleFunctor _ 0).obj
-            ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app _ t)) at he
+        ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app _ t)) at he
     simpa only [Functor.op_obj, τ, ht] using he
   have heq : a' = b' := by
     apply (sheafCompose S.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).map_injective
```

## Status

landed 20261013T145126-L-698155 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep)
