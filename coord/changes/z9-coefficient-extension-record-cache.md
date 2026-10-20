# WeilConjectures.CoefficientExtensionReductionData

## Reason

The previous packet timed out during the required 60 second single-file compile.
Profiling showed repeated comparison of expanded coefficient sheaves and scalar functors
in the concrete structures and their generated declarations, before the three main
proof holes. The repair keeps the same mathematical fields and equations, but generates
four generic records once and specializes them to the actual coefficient constructions.
The two largest proof fields are cached in named, exposed irreducible predicates.
The chain association now has an explicit result type. Comparison definitions are
irreducible but remain exposed, so their original bodies are available to explicit
`unfold` in later proofs. No compiler limit is changed and the module is not split.

The actual field contents, quotient maps, counit, Roos projections, model evaluation
and normalization equations are preserved. The concrete structure names become
abbreviations of the generic records; this changes their generated constructor/projection
names but preserves record notation and field notation used by all current consumers.
`coefficientExtensionSystem` becomes a semireducible definition of the same composite.
No statement in Challenge.lean changes. Targets using these definitions require the
usual statement review of an implementation change; no hypothesis or conclusion changes.

## Old

```lean
structure CoefficientScalarAssociation where
  /-- Ordinary balanced tensor association. -/
  ordinary : A.model.E ⋙ B.model.E ≅ D.model.E
  /-- The balanced formula, including arbitrary coefficients in both factors. -/
  section_formula : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (t • SemilinearSections.scalarExtensionSection.{c, v, r} g B (A.model.E.obj M) U
        (s • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x)) =
      (((g.hom.app U) s * t) • SemilinearSections.scalarExtensionSection.{c, v, r} h D M U x)
  /-- The association in the coherent derived category. -/
  derived : A.T ⋙ B.T ≅ D.T
  /-- It is the localization of the same balanced association on K-flat models. -/
  model : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
    derived.hom.app (DerivedCategory.Q.obj P) ≫ D.model.ε.app P =
      B.T.map (A.model.ε.app P) ≫
        B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)
```

```lean
structure CoefficientScalarUnit {f : R ⟶ R}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f) where
  /-- Ordinary action unitor. -/
  ordinary : A.model.E ≅ 𝟭 (SemilinearSections.Mod.{c, v, max c v r} J R)
  /-- The unitor multiplies the tensor coefficient. -/
  section_formula : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (a • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x) = a • x
  /-- Its derived localization. -/
  derived : A.T ≅ 𝟭 (SemilinearSections.D.{c, v, max c v r} J R)
  /-- The derived unitor is the ordinary one through the canonical K-flat counit. -/
  model : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
    derived.hom.app (DerivedCategory.Q.obj P) =
      A.model.ε.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)
end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})
```

```lean
structure CoefficientExtensionAssociationData where
  /-- Ordinary simultaneous scalar association. -/
  association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n
  /-- On local tensors, (x⊗a)⊗b maps to x⊗ι(a)b. -/
  association_section : IsCoefficientExtensionAssociation l E L ι W A association
```

```lean
structure CoefficientExtensionStrictModel extends
    CoefficientExtensionAssociationData l E L ι W A where
  /-- The direct quotient models as one functor of strict system complexes. -/
  direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
    CochainComplex (coefficientSequenceModules l L W) ℤ
  /-- Its finite values are the actual P tensor B_m, simultaneously. -/
  directEvaluation : ∀ n : ℕ,
    direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n
  /-- The strict transitions are the actual quotient maps on every section. -/
  direct_transition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation
```

```lean
structure CoefficientExtensionReductionData extends
    CoefficientExtensionStrictModel l E L ι W A where
  /-- One coherent representative comparison, natural on the resolving category. -/
  model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q
  /-- This coherent comparison evaluates to derived scalar association through the
  canonical universal counits, using the same P at every level. -/
  model_evaluation : ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
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
  /-- The system is normalized without any boundedness or constructibility condition. -/
  normalized : ∀ K : DerivedCategory (scalarReductionSource l E W),
    IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj K)
  /-- Its total limit is the specified completed scalar extension. -/
  completion : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
    integralScalarExtensionOfUniverses l E L ι W
  /-- The completion identification uses the actual Roos projections on good models. -/
  completion_projection :
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
  /-- The specified coherent counit comparison is an isomorphism. -/
  comparison_isIso : IsIso (coefficientExtensionCounit l E L ι W SE SL A completion)
```

```lean
abbrev coefficientExtensionSystem :
    DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l L W :=
  SE.reduction ⋙ A.scalar.T
```

```lean
def coefficientExtensionAssociationChain (n : ℕ)
    (a : scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI := coefficientExtensionDirectZero l E L ι W n
  letI := coefficientExtensionCompositeZero l E L ι W A n
  (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P
```

```lean
def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n
```

```lean
def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom
```

```lean
def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso
```

```lean
def coefficientExtensionSuccessiveSystemIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        coefficientExtensionSystem l L F j W SL B ≅
      coefficientExtensionSystem l E F (j.comp ι) W SE D :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientExtensionReductionIso l E L ι W SE SL A dEL)
      B.scalar.T ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft SE.reduction a.derived
```

```lean
def coefficientExtensionSuccessiveIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L F j W ≅
      integralScalarExtensionOfUniverses l E F (j.comp ι) W :=
  Functor.isoWhiskerLeft (integralScalarExtensionOfUniverses l E L ι W)
      dLF.completion.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a)
      (coefficientSequenceLimit l F W) ≪≫ dEF.completion
```

## New

The generic record declarations and cached predicates are:

```lean
structure CoefficientScalarComparisonData (Ordinary Derived : Type*)
    (sectionFormula : Ordinary → Prop) (modelFormula : Ordinary → Derived → Prop) where
  ordinary : Ordinary
  section_formula : sectionFormula ordinary
  derived : Derived
  model : modelFormula ordinary derived
```

```lean
structure CoefficientAssociationData (Association : Type*)
    (sectionFormula : Association → Prop) where
  association : Association
  association_section : sectionFormula association
```

```lean
structure CoefficientStrictModelData (Association Direct : Type*)
    (sectionFormula : Association → Prop) (Evaluation : Direct → Type*)
    (transitionFormula : ∀ direct, Evaluation direct → Prop)
    extends CoefficientAssociationData Association sectionFormula where
  direct : Direct
  directEvaluation : Evaluation direct
  direct_transition : transitionFormula direct directEvaluation
```

```lean
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

section ScalarZero
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{r} C] {R S : Sheaf J CommRingCat.{r}} {f : R ⟶ S}
```

```lean
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
```

```lean
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
```

```lean
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
```

```lean
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
end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})
```

```lean
abbrev CoefficientExtensionAssociationData :=
  CoefficientAssociationData
    (∀ n : ℕ, scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (IsCoefficientExtensionAssociation l E L ι W A)
```

```lean
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
```

```lean
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
```

```lean
def coefficientExtensionSystem :
    DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l L W :=
  SE.reduction ⋙ A.scalar.T
```

```lean
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
```

```lean
@[irreducible] def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n
```

```lean
@[irreducible] def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom
```

```lean
@[irreducible] def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso
```

```lean
@[irreducible] def coefficientExtensionSuccessiveSystemIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        coefficientExtensionSystem l L F j W SL B ≅
      coefficientExtensionSystem l E F (j.comp ι) W SE D :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientExtensionReductionIso l E L ι W SE SL A dEL)
      B.scalar.T ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft SE.reduction a.derived
```

```lean
@[irreducible] def coefficientExtensionSuccessiveIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L F j W ≅
      integralScalarExtensionOfUniverses l E F (j.comp ι) W :=
  Functor.isoWhiskerLeft (integralScalarExtensionOfUniverses l E L ι W)
      dLF.completion.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a)
      (coefficientSequenceLimit l F W) ≪≫ dEF.completion
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientExtensionReductionModel | Z9 | All specialized records and comparisons are updated together; three original major theorem holes remain. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | existing claim unaffected; no edits | The only external user of the changed record declarations. It uses d.direct and d.directEvaluation, whose exact types and formulas remain the same. |
| Sheaf.Paper.DerivedPullbackTensorIso | existing claim unaffected; no edits | Direct proof importer; it mentions none of the changed declaration names. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | existing claim unaffected; no edits | Direct proof importer; it mentions none of the changed declaration names. |

`tools/downstream.py --direct --uses` lists the three direct importers above and
only ScalarExtensionTowerCoherence as an external named user. The broader transitive
name-use audit found no additional external uses of any changed name.
The original DerivedPullbackTensorIso consumer compiled against the repaired module in
54.2 seconds. ScalarExtensionTowerCoherence timed out both against this packet and against
the published baseline; it is not edited. IntegralPullbackComparisonRealization likewise timed out against both this packet and
the published baseline; it is not edited. No consumer
statement is adapted or weakened. No direct consumer uses a qualified generated projection
name of the replaced structures; the scalar-tower consumer uses the unchanged field types.

The old public imports IntegralReductionTowerCanonical and
CompletedIntegralConstantMapOfUniverses are unnecessary for this module's statements.
Their declarations are not withdrawn; external users of their names continue to import
their own interfaces. The direct importers above use no declaration from these two
interfaces through this item. The removed private proof imports remain the dependency
plan of the three untouched major theorem holes, and are not claimed to be pruned nodes.

## Status

landed 20261020T221411-L-4184053 2026-10-20 (merge of deliver/Z9/Sheaf.Paper.CoefficientExtensionReductionModel)
