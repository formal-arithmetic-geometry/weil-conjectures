# AlgebraicGeometry.Etale.normalizationRestrictionComplex and normalizationRestrictedIso

## Reason

The complete restriction proof needs stable names for the prescribed complex,
augmentation and resolution comparison. The complex is literally
I.cochainComplex and the augmentation is literally I.ι', using the original
canonical Mathlib structures. The restricted augmentation, its quasi-isomorphism
proof and the K-injectivity proof retain their original implementations. No
object is selected from an existence theorem.

All 23 original written public signatures and all original public imports are
retained. The normalization isomorphism has the same three factors. Cohomology
pullback names its original coefficient composite through a generic single-complex
construction. The original AddMonoidHom.mk' class component and sheafification
lift are retained. A generic opposite-category constructor bundles the same
components as the original kappa. Generic proved helpers avoid repeating the
large concrete-category conversions in the additivity and naturality proofs.

The semantic audit compares the complex, augmentation, restricted augmentation,
the full normalization isomorphism and cohomology pullback with their prescribed
expressions. The class component is byte-identical to its original definition;
kappa bundles the same components. Actual consumers are checked against these
definitions. Their statements retain their original meaning. Definitions below
targets are affected, so their semantic acceptance review is reopened. No adopted
source-library file, target statement or unit route changes.

## Old

```lean
noncomputable def normalizationRestrictionComplex {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  ((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

noncomputable def normalizationPresheafComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj
    (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)

noncomputable def normalizationRestrictedIso {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ≅
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) :=
  (normalizationRestrictedResolution
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I).homologyRightDerivedFunctorObjIso
      (Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) ≪≫
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    ((NatIso.mapHomologicalComplex
      (normalizationSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
      (.up ℤ)).app I.cochainComplex) ≪≫
  ((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
    ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))

noncomputable def normalizationCohomologyRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (t : V' ⟶ V) :
    rawAffineRestrictedCohomology f q F V ⟶ rawAffineRestrictedCohomology f q F V' :=
  rawAffineComplexPullback (q : ℤ) (normalizationChartMap f t)
      ((CochainComplex.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F)) ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{u + 1}
            (normalizationChartMap f t)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
          (CochainComplex.singleFunctor _ 0).map
            ((upperStarComp AddCommGrpCat.{u + 1} (normalizationChartMap f t)
              (pullback.snd V.hom f) (pullback.snd V'.hom f)
              (MorphismProperty.Over.w
                ((MorphismProperty.Over.pullback @Etale ⊤ f).map t)).symm).inv.app F)))

theorem normalizationClass_add {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (z z' : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :
    abelianHigherDirectImageClass f q F V (z + z') =
      abelianHigherDirectImageClass f q F V z + abelianHigherDirectImageClass f q F V z' := by
  let c := toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
    (canonicalComparison f q F).hom.hom
  have h := (c.app (op V)).hom.map_add z z'
  change (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) (z + z') =
    (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) z +
    (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) z' at h
  simpa only [canonicalComparison_class] using h

theorem normalizationKappaComponent_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (abelianHigherDirectImageRawPresheaf f q F).map t ≫
        normalizationKappaComponent f q F V'.unop =
      normalizationKappaComponent f q F V.unop ≫
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.map t := by
  let c := toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
    (canonicalComparison f q F).hom.hom
  have hc (U : S.Etale) : normalizationKappaComponent f q F U = c.app (op U) := by
    ext z
    exact (canonicalComparison_class f q F U z).symm
  rw [hc, hc]
  exact c.naturality t

noncomputable def normalizationKappa {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    abelianHigherDirectImageRawPresheaf f q F ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj where
  app V := normalizationKappaComponent f q F V.unop
  naturality _ _ t := normalizationKappaComponent_naturality f q F t
```

## New

```lean
noncomputable def normalizationBaseComplex {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  I.cochainComplex

noncomputable def normalizationBaseAugmentation {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor _ 0).obj F ⟶ normalizationBaseComplex F I :=
  I.ι'

noncomputable def normalizationChartResolutionIso {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ≅
      (((Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj (normalizationRestrictionComplex
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I)).homology (q : ℤ) :=
  (normalizationRestrictedResolution
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I).homologyRightDerivedFunctorObjIso
      (Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)

noncomputable def normalizationSingleCoefficientMap
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms D] [HasZeroMorphisms E] [HasZeroObject D] [HasZeroObject E]
    (A : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E)
    [A.PreservesZeroMorphisms] (e : H ≅ G ⋙ A) (F : C) :=
  (HomologicalComplex.singleMapHomologicalComplex A (.up ℤ) 0).hom.app (G.obj F) ≫
    (HomologicalComplex.single E (.up ℤ) 0).map (e.inv.app F)

noncomputable def normalizationRestrictionCoefficientMap {X : Scheme.{u}}
    {W W' : X.Etale} (b : W' ⟶ W)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  normalizationSingleCoefficientMap (upperStar AddCommGrpCat.{u + 1} b.left)
    (upperStar AddCommGrpCat.{u + 1} W.hom) (upperStar AddCommGrpCat.{u + 1} W'.hom)
    (upperStarComp AddCommGrpCat.{u + 1} b.left W.hom W'.hom b.w.symm) F

def normalizationOpNaturalTransformation
    {C D : Type*} [Category C] [Category D] (P Q : Cᵒᵖ ⥤ D)
    (a : ∀ U : C, P.obj (op U) ⟶ Q.obj (op U))
    (ha : ∀ {U V : Cᵒᵖ} (t : U ⟶ V), P.map t ≫ a V.unop = a U.unop ≫ Q.map t) :
    P ⟶ Q where
  app U := a U.unop
  naturality _ _ t := ha t

noncomputable def normalizationRestrictionComplex {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  ((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
    (normalizationBaseComplex F I)

noncomputable def normalizationPresheafComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj
    (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj
      (normalizationBaseComplex F I))

noncomputable def normalizationRestrictedIso {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ≅
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) :=
  normalizationChartResolutionIso f q F I V ≪≫
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    ((NatIso.mapHomologicalComplex
      (normalizationSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
      (.up ℤ)).app (normalizationBaseComplex F I)) ≪≫
  ((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
    ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))

noncomputable def normalizationCohomologyRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (t : V' ⟶ V) :
    rawAffineRestrictedCohomology f q F V ⟶ rawAffineRestrictedCohomology f q F V' :=
  rawAffineComplexPullback (q : ℤ) (normalizationChartMap f t)
      ((CochainComplex.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F)) ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
      (DerivedCategory.Q.map
        (normalizationRestrictionCoefficientMap
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map t) F))

theorem normalizationClass_add {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (z z' : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :
    abelianHigherDirectImageClass f q F V (z + z') =
      abelianHigherDirectImageClass f q F V z + abelianHigherDirectImageClass f q F V z' := by
  exact additive_of_component (abelianHigherDirectImageClass f q F V)
    ((toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
      (canonicalComparison f q F).hom.hom).app (op V))
    (canonicalComparison_class f q F V) z z'

theorem normalizationKappaComponent_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (abelianHigherDirectImageRawPresheaf f q F).map t ≫
        normalizationKappaComponent f q F V'.unop =
      normalizationKappaComponent f q F V.unop ≫
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.map t := by
  apply naturality_of_op_components
    (toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
      (canonicalComparison f q F).hom.hom)
    (normalizationKappaComponent f q F) _ t
  intro U
  ext z
  exact (canonicalComparison_class f q F U z).symm

noncomputable def normalizationKappa {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    abelianHigherDirectImageRawPresheaf f q F ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj :=
  normalizationOpNaturalTransformation _ _ (normalizationKappaComponent f q F)
    (fun t ↦ normalizationKappaComponent_naturality f q F t)
```

## Users

The original-declaration scan covers all 23 original names with tools/downstream.py
--uses. Unrelated declarations named normalizationLift are excluded after reading
their namespaces. Current holder records were read on 2026-10-26.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData | unclaimed | construction sharing; original signatures retained |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionRestriction | K4 | assigned proof; statement retained |
| Sheaf.AlgebraicGeometry.CoherentHigherImageModuleAction | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionClass | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionCocycle | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionNaturality | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.ResolutionCocycleAdjunctionClass | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormula | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.UnitScalarRawData | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.UnitScalarRawEvaluation | unclaimed | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.SheafHDerivedPullback | E3 | original consumer; statement retained |
| Sheaf.AlgebraicGeometry.ResolutionSectionCocycleSheafification | unclaimed | original consumer; statement retained |

Consumer validation completed without Lean errors. Eight consumers passed the
per-file limit; the four timing failures also occur against the unmodified
published library. The exact comparisons are recorded in report.md. No consumer
adaptation is included.

## Status

landed 20261026T091912-L-3385309 2026-10-26 (merge of deliver/K4/Sheaf.AlgebraicGeometry.RawRestrictedResolutionRestriction)
