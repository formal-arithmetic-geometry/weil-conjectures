# CategoryTheory.sheafification_sections_local

## Reason

The original intermediate statement is already STATEMENT-DISPUTED. Its unrestricted value
universe admits the false small-subterminal reflector described in the U2 report. The Stacks
plus construction uses a set universe containing the site data. Restore that convention with
C : Type u, Category.{w} C, and values Type (max u w). Unlike assuming local injectivity as an
extra premise, this convention obtains it from Mathlib's proved plus comparison.
All three conclusions and all site axioms remain. Generalizing SmallCategory to Category also
allows different object and morphism universes. This does not prove the false original theorem.
The private helpers retain their content and now accept Category.{v} C so they work in the
corrected public theorem. No target or definition changes, so target definition review is not
reopened. The unit sk-thm-p1 does not realize this node; its route stays.

## Old

```lean
theorem sheafification_sections_local
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasWeakSheafify J.toGrothendieck (Type w)]
    (F : Cᵒᵖ ⥤ Type w) :
    (∀ (U : C) (s : (sheafify J.toGrothendieck F).obj (op U)),
      ∃ (S : Presieve U) (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
        S ∈ J U ∧
        (∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
        (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
          (hf : S f) (hg : S g),
          ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
            ∃ (T : Presieve Z), T ∈ J Z ∧
              ∀ (Y : C) (h : Y ⟶ Z), T h →
                F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg))) ∧
    (∀ (U : C) (S : Presieve U) (_ : S ∈ J U)
      (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
      (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
        (hf : S f) (hg : S g),
        ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
          ∃ (T : Presieve Z), T ∈ J Z ∧
            ∀ (Y : C) (h : Y ⟶ Z), T h →
              F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg)) →
      ∃! s : (sheafify J.toGrothendieck F).obj (op U),
        ∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
    (∀ (U : C) (p q : F.obj (op U)),
      (toSheafify J.toGrothendieck F).app (op U) p = (toSheafify J.toGrothendieck F).app (op U) q →
      ∃ (S : Presieve U), S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U) (_ : S f),
          F.map f.op p = F.map f.op q)
```

## New

```lean
theorem sheafification_sections_local
    {C : Type u} [Category.{w} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasWeakSheafify J.toGrothendieck (Type (max u w))]
    (F : Cᵒᵖ ⥤ Type (max u w)) :
    (∀ (U : C) (s : (sheafify J.toGrothendieck F).obj (op U)),
      ∃ (S : Presieve U) (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
        S ∈ J U ∧
        (∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
        (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
          (hf : S f) (hg : S g),
          ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
            ∃ (T : Presieve Z), T ∈ J Z ∧
              ∀ (Y : C) (h : Y ⟶ Z), T h →
                F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg))) ∧
    (∀ (U : C) (S : Presieve U) (_ : S ∈ J U)
      (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
      (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
        (hf : S f) (hg : S g),
        ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
          ∃ (T : Presieve Z), T ∈ J Z ∧
            ∀ (Y : C) (h : Y ⟶ Z), T h →
              F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg)) →
      ∃! s : (sheafify J.toGrothendieck F).obj (op U),
        ∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
    (∀ (U : C) (p q : F.obj (op U)),
      (toSheafify J.toGrothendieck F).app (op U) p =
        (toSheafify J.toGrothendieck F).app (op U) q →
      ∃ (S : Presieve U), S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U) (_ : S f),
          F.map f.op p = F.map f.op q)
```

## Users

The downstream scan lists 667 importers, but its --uses result and a whole-library
search find no applications of sheafification_sections_local outside its declaration.
No dependent signature mentions it and no dependent proof applies it. The following complete
import-closure table records the result for each downstream module. No adapted module is
included. The seven DAG citers are separately assessed in the node's statement_change:

- `lem-sbc-cyclic-higher-direct-image-local-vanishing`: holds=true. Only local surjectivity is used. The site and underlying abelian values are in the adequate u+1 universe; its statement is unchanged.
- `lem-weil-pbc-constant-sheaf-sections-locally-constant`: holds=false. The landed Lean signature uses AddCommGrpCat.{u} on an etale category whose objects live in u+1. The corrected theorem cannot directly justify its planned local-equality step at those sizes. A bridge via an essentially small affine-etale site (or another direct proof) is needed; this delivery leaves its signature and proof untouched.
- `lem-weil-pbc-image-presheaf-sheafification-iso`: holds=false. Its unrestricted Type w values and Category.{v} C do not meet the corrected local-injectivity size convention. Its planned last-clause use requires its own size or local-injectivity correction; the original Boolean-site counterexample also obstructs its current generality. The module is not adapted because it currently makes no application and compiles unchanged.
- `lem-weil-pbc-module-sheaf-constant-ring-equivalence`: holds=true. The small etale site objects and coefficient values lie in u+1; scalar units already have local injectivity and surjectivity from Mathlib. No application of the changed declaration occurs.
- `lem-weil-pbc-sheaf-cokernel-local-image`: holds=true. The opens site has objects and section values in Type u, and small morphisms. Local equality and representation apply in this common universe; module-to-sets identification remains a separate dependency.
- `lem-weil-pbc-sheaves-injective-directed-colimit-qc-sections`: holds=true. Opens X and the Type u-valued presheaf colimit have the common u universe. Both representation and local equality are available with all clauses unchanged.
- `lem-weil-pbc-site-module-sheafification-lift-injective`: holds=true. Its proof uses only local representations. The general image-subsheaf surjectivity argument remains valid in arbitrary value universes; its WEqualsLocallyBijective assumption also supplies the needed module unit properties. No existing declaration application needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SiteSheafificationSectionsLocal | P3 | Corrected theorem proved; private helpers generalized in their site morphism universe. |
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChange | Z2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionIsos | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedCounitHomologyFactorization | M2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedUnitHomologyFactorization | R2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedConcentration | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison | Z2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSinglePushforwardUnitIso | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | N2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleIdealSection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AmplePullbackIdealAffineSection | T2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeMapCech | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | A2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CechResolution | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentProjRepresentation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes | Y3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentSerreVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentSupportedAffineSection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantModuleHigherDirectImageCyclicReduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClassCore | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | J3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | R1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | T2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericTorsionCohomologyColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericTorsionColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | P2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CyclicHigherDirectImageLocalVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageCohomologyCoproduct | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageCoproductAffineTruncation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageTruncatedCoproduct | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageUniformAffineTruncation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedGlobalSectionsCohomologyCoproduct | H1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTorIndependentFlatComplex | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedTensorUnitCompact | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | Q2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | P2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleBaseChangeRestrictScalars | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFilteredInjectiveAcyclic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleInjectiveColimitAcyclic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAcyclic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSectionColimitEventualZero | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSectionColimitRepresentative | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSectionsFilteredColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffinePushforwardIdealDevissage | C2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | N3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardCoherent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRestrictionDerivedRightAdjoint | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSheafHomAffine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | T2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistedInverseBoundedBelow | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatModuleDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFibreCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsCompleteBase | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteFibreVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteSchemeSplitting | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | R3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsSeparable | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | H2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GradedSerreVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom | T2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | H3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | B3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | S1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.IntersectionNumber | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulAffineDetection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality | V1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | V2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LerayDegenerateSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LerayEdgeVanishingIso | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LerayLowDegree | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LeraySpectralSequence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LocallyFreeExtNaturality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianStalkExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMap | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1 | X2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Modules.VeryAmpleDisjointUnion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedImmersionOfSurjectiveStructureStalks | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianPerfectDirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts | P2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictionSupportTriangle | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallGluing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallGluingCore | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | S3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | Q2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDualityPairingNaturality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperDirectImageFiniteTor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | E1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectDirectImagePerfect | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackIsoPrimeTorsionDevissage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackIsoTorsionColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.PushforwardRankOnOpen | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QcOpenDerivedLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsCohomologyFiniteSubsumRepresentatives | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeSerreVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedCohomologyColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SerreCriterionAffineness | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SerreSectionCoordinateSurjective | R3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleComponentFinite | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleFinite | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleTailFinite | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | Z2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | Z2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing | U2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitReductionSpectrumComponents | R1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | B2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TheoremFormalFunctions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningAffineScheme | V2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningIntegral | D2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TruncatedDirectImageAffineFiniteSupport | V1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TwistedSectionFiniteCoordinates | V2 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.UniformDirectImageBoundCore | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.VanishingProjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.BaseChangeClosureComponents | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.CechCupPullbackCompat | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.CechNerveFreeHomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.CechRefinementCochainMap | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.ConstantSheafSectionsLocallyConstant | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.EtaleShriekToStarInjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.EulerCharacteristicWellDefined | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraLift | U3 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.FiniteStructureProperSupport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.FiniteSurjectiveCoherentGenericSupport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.GradedFinitenessCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.HigherDirectImagePresheaf | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyAbelian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyModule | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverFreeResolution | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.ImagePresheafSheafificationIso | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.MLCohomologyPowersIdeal | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparisonSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.SiteModuleSheafificationLiftInjective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Topology.SheafCokernelLocalImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Topology.SheafDirectedColimitFiniteCoequalizers | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Topology.SheafFiniteRelationTruncations | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Topology.SheafFiniteTruncationColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Topology.SheavesInjectiveDirectedColimitSections | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| Sheaf.Topology.SpectralSheafColimitConstantEmbeddings | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| TargetsCheck | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex | M2 | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocus | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections | J1 | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Projective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Serre | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | B3 | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | F1 | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Modules.AffineHom | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Modules.Ample | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Degree | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.RationalPoint | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Representability | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | M1 | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration use; statements and definitions unaffected; no adaptation. |

## Status

landed 20261012T135302-L-1685823 2026-10-12 (merge of deliver/P3/Sheaf.Paper.SiteSheafificationSectionsLocal)
