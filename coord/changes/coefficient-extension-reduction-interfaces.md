# Coefficient-extension reduction interfaces

## Reason

Construction lemmas need the model records without importing the theorem that uses them.
Move existing public declarations verbatim from CoefficientExtensionReductionModel to
CoefficientExtensionReductionData, and publicly import the latter from the former.
This prevents an import cycle. No target, definition, signature or meaning changes.
No consumer adaptation is needed; no source-library declaration is modified.
The relocated declarations include no new choice of data and no proof holes.

## Old

The following declarations were in `lean/Sheaf/Paper/CoefficientExtensionReductionModel.lean`.
Their original variable contexts and docstrings are preserved in the new module.

```lean
structure CoefficientScalarComparisonData (Ordinary Derived : Type*)
    (sectionFormula : Ordinary → Prop) (modelFormula : Ordinary → Derived → Prop) where
  ordinary : Ordinary
  section_formula : sectionFormula ordinary
  derived : Derived
  model : modelFormula ordinary derived

structure CoefficientAssociationData (Association : Type*)
    (sectionFormula : Association → Prop) where
  association : Association
  association_section : sectionFormula association

structure CoefficientStrictModelData (Association Direct : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop)
    extends CoefficientAssociationData Association sectionFormula where
  direct : Direct
  directEvaluation : Evaluation direct
  direct_transition : transitionFormula direct directEvaluation

structure CoefficientReductionModelData (Association Direct Completion : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop) (Model : Direct → Type*)
    (modelFormula : Association → ∀ direct, Evaluation direct → Model direct → Prop)
    (Normalized : Prop)
    (completionFormula : ∀ direct, Evaluation direct → Model direct → Completion → Prop)
    (comparisonFormula : Completion → Prop)
    extends CoefficientStrictModelData Association Direct sectionFormula Evaluation
      transitionFormula where
  model : Model direct
  model_evaluation : modelFormula association direct directEvaluation model
  normalized : Normalized
  completion : Completion
  completion_projection : completionFormula direct directEvaluation model completion
  comparison_isIso : comparisonFormula completion

instance coefficientScalarModelZero (A : SemilinearSections.ScalarData.{c, v, r} f) :
    A.model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ A.model.E A.model.additive

abbrev CoefficientScalarAssociation :=
  CoefficientScalarComparisonData (A.model.E ⋙ B.model.E ≅ D.model.E) (A.T ⋙ B.T ≅ D.T)
    (fun ordinary ↦ ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
      (s : S.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (t • SemilinearSections.scalarExtensionSection.{c, v, r} g B (A.model.E.obj M) U
          (s • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x)) =
        (((g.hom.app U) s * t) •
          SemilinearSections.scalarExtensionSection.{c, v, r} h D M U x))
    (fun ordinary derived ↦ ∀
      (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
      derived.hom.app (DerivedCategory.Q.obj P) ≫ D.model.ε.app P =
        B.T.map (A.model.ε.app P) ≫
          B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

abbrev CoefficientScalarUnit {f : R ⟶ R}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f) :=
  CoefficientScalarComparisonData
    (A.model.E ≅ 𝟭 (SemilinearSections.Mod.{c, v, max c v r} J R))
    (A.T ≅ 𝟭 (SemilinearSections.D.{c, v, max c v r} J R))
    (fun ordinary ↦ ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
      (a : R.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (a • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x) = a • x)
    (fun ordinary derived ↦ ∀
      (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
      derived.hom.app (DerivedCategory.Q.obj P) =
        A.model.ε.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

theorem coefficientExtensionQuotient_naturality (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι W (n + 1) ≫
        coefficientSequenceCommRingTransition l L W n =
      coefficientSequenceCommRingTransition l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n := by
  let forgetComm := sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat RingCat)
  unfold coefficientSequenceCommRingTransition integralScalarQuotientSheafMap
  apply forgetComm.map_injective
  change forgetComm.map _ ≫ forgetComm.map _ =
    forgetComm.map _ ≫ forgetComm.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← forgetComm.map_comp]
  apply congrArg (fun z ↦ forgetComm.map z)
  rw [← (constantSheaf (Scheme.ProEt.topology W) CommRingCat).map_comp]
  congr 1
  exact quotientRing_transition l E L ι n

abbrev CoefficientExtensionSystems :=
  SemilinearSections.ScalarSystems.{t + 1, t, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)

def coefficientExtensionSystem :
    DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l L W :=
  SE.reduction ⋙ A.scalar.T

@[irreducible] def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom

instance coefficientExtensionFiniteAdditive (n : ℕ) : ((A.levels n).model.E).Additive :=
  (A.levels n).model.additive

instance coefficientExtensionFiniteZero (n : ℕ) :
    (A.levels n).model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (A.levels n).model.additive

instance coefficientExtensionReductionZero (n : ℕ) :
    (scalarReductionExtension l E W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (coefficientFiniteExtensionAdditive l E W n)

instance coefficientExtensionDirectZero (n : ℕ) :
    (integralScalarReduction l E L ι W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (integralScalarReduction_additive l E L ι W n)

instance coefficientExtensionCompositeZero (n : ℕ) :
    (scalarReductionExtension l E W n ⋙ (A.levels n).model.E).PreservesZeroMorphisms :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  Functor.preservesZeroMorphisms_comp _ _

@[irreducible] def coefficientExtensionAssociationChain (n : ℕ)
    (a : scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (((scalarReductionExtension l E W n ⋙ (A.levels n).model.E).mapHomologicalComplex
      (.up ℤ)).obj P) ⟶
      (((integralScalarReduction l E L ι W n).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI := coefficientExtensionDirectZero l E L ι W n
  letI := coefficientExtensionCompositeZero l E L ι W A n
  (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P

@[irreducible] def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n

def IsCoefficientExtensionAssociation
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n) : Prop :=
  ∀ (n : ℕ) (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U),
    ((association n).hom.app M).val.app U
      (b • SemilinearSections.scalarExtensionSection.{t + 1, t, u}
        (integralScalarQuotientSheafMap l E L ι W n) (A.levels n)
        ((scalarReductionExtension l E W n).obj M) U
        (a • @id (((scalarReductionExtension l E W n).obj M).val.obj U)
          (((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app U x))) =
      integralScalarTensorSection l E L ι W n M U
        (((integralScalarQuotientSheafMap l E L ι W n).hom.app U) a * b) x

abbrev CoefficientExtensionAssociationData :=
  CoefficientAssociationData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (IsCoefficientExtensionAssociation l E L ι W A)

def IsCoefficientExtensionStrictTransition
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceEvaluation l L W (n + 1)).obj
      ((direct.obj P).X i)).val.obj U)),
    HEq ((((coefficientSequenceTransition l L W (Nat.le_succ n)).app
        ((direct.obj P).X i)).val.app U).hom x)
      (((((directEvaluation n).inv.app P).f i).val.app U).hom
        ((((integralScalarTransition l E L ι W n).app P.obj).f i).val.app U
          ((((directEvaluation (n + 1)).hom.app P).f i).val.app U x)))

abbrev CoefficientExtensionStrictModel :=
  CoefficientStrictModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)

@[irreducible] def IsCoefficientExtensionModelEvaluation
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
        (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
          (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P) =
      (A.evaluation n).hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map ((SE.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom ≫
        (A.levels n).model.ε.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map
          (coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj)

@[irreducible] def IsCoefficientExtensionCompletionProjection
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (completion : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    completion.inv.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceProjection l L W n).app
          ((coefficientExtensionSystem l E L ι W SE A).obj (DerivedCategory.Q.obj P.obj)) ≫
        (coefficientFiniteDerivedRestriction l L W n).map
          ((coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
            (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
              (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) ≫
        (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
          ((integralScalarFiniteComplex l E L ι W n).obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        DerivedCategory.Q.map
          (coefficientExtensionRoosProjection l E L ι W P.obj n)

abbrev CoefficientExtensionReductionData :=
  CoefficientReductionModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)
    (fun direct ↦ integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (IsCoefficientExtensionModelEvaluation l E L ι W SE A)
    (∀ K : DerivedCategory (scalarReductionSource l E W),
    IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj K))
    (IsCoefficientExtensionCompletionProjection l E L ι W SE A)
    (fun completion ↦ IsIso (coefficientExtensionCounit l E L ι W SE SL A completion))

@[irreducible] def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso

def CoefficientExtensionReductionSkeleton :=
  CoefficientReductionModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)
    (fun direct ↦ integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (IsCoefficientExtensionModelEvaluation l E L ι W SE A)
    (∀ K : DerivedCategory (scalarReductionSource l E W),
      IsNormalizedCoefficientSequence l L W
        ((coefficientExtensionSystem l E L ι W SE A).obj K))
    (IsCoefficientExtensionCompletionProjection l E L ι W SE A)
    (fun _ ↦ True)
```

## New

Identical declarations now in `lean/Sheaf/Paper/CoefficientExtensionReductionData.lean`.
The original module adds `public import Sheaf.Paper.CoefficientExtensionReductionData`
and retains its four existing public imports.

```lean
structure CoefficientScalarComparisonData (Ordinary Derived : Type*)
    (sectionFormula : Ordinary → Prop) (modelFormula : Ordinary → Derived → Prop) where
  ordinary : Ordinary
  section_formula : sectionFormula ordinary
  derived : Derived
  model : modelFormula ordinary derived

structure CoefficientAssociationData (Association : Type*)
    (sectionFormula : Association → Prop) where
  association : Association
  association_section : sectionFormula association

structure CoefficientStrictModelData (Association Direct : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop)
    extends CoefficientAssociationData Association sectionFormula where
  direct : Direct
  directEvaluation : Evaluation direct
  direct_transition : transitionFormula direct directEvaluation

structure CoefficientReductionModelData (Association Direct Completion : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop) (Model : Direct → Type*)
    (modelFormula : Association → ∀ direct, Evaluation direct → Model direct → Prop)
    (Normalized : Prop)
    (completionFormula : ∀ direct, Evaluation direct → Model direct → Completion → Prop)
    (comparisonFormula : Completion → Prop)
    extends CoefficientStrictModelData Association Direct sectionFormula Evaluation
      transitionFormula where
  model : Model direct
  model_evaluation : modelFormula association direct directEvaluation model
  normalized : Normalized
  completion : Completion
  completion_projection : completionFormula direct directEvaluation model completion
  comparison_isIso : comparisonFormula completion

instance coefficientScalarModelZero (A : SemilinearSections.ScalarData.{c, v, r} f) :
    A.model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ A.model.E A.model.additive

abbrev CoefficientScalarAssociation :=
  CoefficientScalarComparisonData (A.model.E ⋙ B.model.E ≅ D.model.E) (A.T ⋙ B.T ≅ D.T)
    (fun ordinary ↦ ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
      (s : S.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (t • SemilinearSections.scalarExtensionSection.{c, v, r} g B (A.model.E.obj M) U
          (s • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x)) =
        (((g.hom.app U) s * t) •
          SemilinearSections.scalarExtensionSection.{c, v, r} h D M U x))
    (fun ordinary derived ↦ ∀
      (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
      derived.hom.app (DerivedCategory.Q.obj P) ≫ D.model.ε.app P =
        B.T.map (A.model.ε.app P) ≫
          B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

abbrev CoefficientScalarUnit {f : R ⟶ R}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f) :=
  CoefficientScalarComparisonData
    (A.model.E ≅ 𝟭 (SemilinearSections.Mod.{c, v, max c v r} J R))
    (A.T ≅ 𝟭 (SemilinearSections.D.{c, v, max c v r} J R))
    (fun ordinary ↦ ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
      (a : R.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (a • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x) = a • x)
    (fun ordinary derived ↦ ∀
      (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
      derived.hom.app (DerivedCategory.Q.obj P) =
        A.model.ε.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

theorem coefficientExtensionQuotient_naturality (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι W (n + 1) ≫
        coefficientSequenceCommRingTransition l L W n =
      coefficientSequenceCommRingTransition l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n := by
  let forgetComm := sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat RingCat)
  unfold coefficientSequenceCommRingTransition integralScalarQuotientSheafMap
  apply forgetComm.map_injective
  change forgetComm.map _ ≫ forgetComm.map _ =
    forgetComm.map _ ≫ forgetComm.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← forgetComm.map_comp]
  apply congrArg (fun z ↦ forgetComm.map z)
  rw [← (constantSheaf (Scheme.ProEt.topology W) CommRingCat).map_comp]
  congr 1
  exact quotientRing_transition l E L ι n

abbrev CoefficientExtensionSystems :=
  SemilinearSections.ScalarSystems.{t + 1, t, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)

def coefficientExtensionSystem :
    DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l L W :=
  SE.reduction ⋙ A.scalar.T

@[irreducible] def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom

instance coefficientExtensionFiniteAdditive (n : ℕ) : ((A.levels n).model.E).Additive :=
  (A.levels n).model.additive

instance coefficientExtensionFiniteZero (n : ℕ) :
    (A.levels n).model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (A.levels n).model.additive

instance coefficientExtensionReductionZero (n : ℕ) :
    (scalarReductionExtension l E W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (coefficientFiniteExtensionAdditive l E W n)

instance coefficientExtensionDirectZero (n : ℕ) :
    (integralScalarReduction l E L ι W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (integralScalarReduction_additive l E L ι W n)

instance coefficientExtensionCompositeZero (n : ℕ) :
    (scalarReductionExtension l E W n ⋙ (A.levels n).model.E).PreservesZeroMorphisms :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  Functor.preservesZeroMorphisms_comp _ _

@[irreducible] def coefficientExtensionAssociationChain (n : ℕ)
    (a : scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (((scalarReductionExtension l E W n ⋙ (A.levels n).model.E).mapHomologicalComplex
      (.up ℤ)).obj P) ⟶
      (((integralScalarReduction l E L ι W n).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI := coefficientExtensionDirectZero l E L ι W n
  letI := coefficientExtensionCompositeZero l E L ι W A n
  (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P

@[irreducible] def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n

def IsCoefficientExtensionAssociation
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n) : Prop :=
  ∀ (n : ℕ) (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U),
    ((association n).hom.app M).val.app U
      (b • SemilinearSections.scalarExtensionSection.{t + 1, t, u}
        (integralScalarQuotientSheafMap l E L ι W n) (A.levels n)
        ((scalarReductionExtension l E W n).obj M) U
        (a • @id (((scalarReductionExtension l E W n).obj M).val.obj U)
          (((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app U x))) =
      integralScalarTensorSection l E L ι W n M U
        (((integralScalarQuotientSheafMap l E L ι W n).hom.app U) a * b) x

abbrev CoefficientExtensionAssociationData :=
  CoefficientAssociationData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (IsCoefficientExtensionAssociation l E L ι W A)

def IsCoefficientExtensionStrictTransition
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceEvaluation l L W (n + 1)).obj
      ((direct.obj P).X i)).val.obj U)),
    HEq ((((coefficientSequenceTransition l L W (Nat.le_succ n)).app
        ((direct.obj P).X i)).val.app U).hom x)
      (((((directEvaluation n).inv.app P).f i).val.app U).hom
        ((((integralScalarTransition l E L ι W n).app P.obj).f i).val.app U
          ((((directEvaluation (n + 1)).hom.app P).f i).val.app U x)))

abbrev CoefficientExtensionStrictModel :=
  CoefficientStrictModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)

@[irreducible] def IsCoefficientExtensionModelEvaluation
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
        (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
          (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P) =
      (A.evaluation n).hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map ((SE.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom ≫
        (A.levels n).model.ε.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map
          (coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj)

@[irreducible] def IsCoefficientExtensionCompletionProjection
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (completion : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    completion.inv.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceProjection l L W n).app
          ((coefficientExtensionSystem l E L ι W SE A).obj (DerivedCategory.Q.obj P.obj)) ≫
        (coefficientFiniteDerivedRestriction l L W n).map
          ((coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
            (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
              (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) ≫
        (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
          ((integralScalarFiniteComplex l E L ι W n).obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        DerivedCategory.Q.map
          (coefficientExtensionRoosProjection l E L ι W P.obj n)

abbrev CoefficientExtensionReductionData :=
  CoefficientReductionModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)
    (fun direct ↦ integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (IsCoefficientExtensionModelEvaluation l E L ι W SE A)
    (∀ K : DerivedCategory (scalarReductionSource l E W),
    IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj K))
    (IsCoefficientExtensionCompletionProjection l E L ι W SE A)
    (fun completion ↦ IsIso (coefficientExtensionCounit l E L ι W SE SL A completion))

@[irreducible] def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso

def CoefficientExtensionReductionSkeleton :=
  CoefficientReductionModelData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    ((integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W)
    (IsCoefficientExtensionAssociation l E L ι W A)
    (fun direct ↦ ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (IsCoefficientExtensionStrictTransition l E L ι W)
    (fun direct ↦ integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q)
    (IsCoefficientExtensionModelEvaluation l E L ι W SE A)
    (∀ K : DerivedCategory (scalarReductionSource l E W),
      IsNormalizedCoefficientSequence l L W
        ((coefficientExtensionSystem l E L ι W SE A).obj K))
    (IsCoefficientExtensionCompletionProjection l E L ι W SE A)
    (fun _ ↦ True)
```

## Users

All transitive consumers reported by `tools/downstream.py --uses` and all new consumers
are listed. Only the original item and ScalarExtensionTowerCoherence name the moved
declarations in the existing tree. The latter is quarantined: its attachment, source
and dependencies are preserved. Identical bodies preserve all target meanings.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CoefficientExtensionFiniteAssociation` | unclaimed | New construction consumer of the shared interface. |
| `Sheaf.Paper.CoefficientExtensionReductionData` | unclaimed | New construction consumer of the shared interface. |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | E6 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CoefficientExtensionRepresentativeRoos` | unclaimed | New construction consumer of the shared interface. |
| `Sheaf.Paper.CoefficientExtensionRestrictedTower` | unclaimed | New construction consumer of the shared interface. |
| `Sheaf.Paper.CoefficientExtensionStrictRepresentatives` | unclaimed | New construction consumer of the shared interface. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ConstructibleRationalHomComparison` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | Y6 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | A4 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | Y7 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | Y8 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteProjectionActionLaws` | G2 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FiniteProperProductTranspose` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | B3 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | G3 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | A5 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | E9 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.LocalizedTensorBraidingNaturality` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | U4 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PointExactDerivedModel` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PointTransformationCoefficientDescent` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PurityFiniteOpenIntervalDescent` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Uses CoefficientExtensionSystems and CoefficientExtensionReductionData unchanged; quarantined source retained and not edited. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | M5 | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | Identical declarations reexported; signatures, bodies and meaning unchanged. |

## Status

landed 20261021T233647-L-845381 2026-10-21 (merge of deliver/E6/Sheaf.Paper.CoefficientExtensionReductionModel)
