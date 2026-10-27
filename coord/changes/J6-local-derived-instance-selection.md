# WeilConjectures.coefficientOrdinaryQuotientComponent

## Reason

Repair of returned head `adf7546a9e3`, findings 2, 2b and H10. The shared tensor,
completed ring, scalar-comparison predicates and change-of-rings statements are
restored without any edits to their modules. All 92 existing declaration headers,
structure fields and public imports match current source. All 154 existing compiled
declaration and structure-field types have identical expression hashes to current
source. All 92 universe-parameter lists also agree. No binder, universe parameter,
hypothesis or conclusion changes.

The changes below package repeated terms inside the item. The ordinary quotient
component evaluates one named natural transformation and its recorded ordinary
adjunction. The source theorem fixes the unit on every local section, which
determines the adjunction for these fixed functors; the helper retains the very
same choice term. Tower sections use the same underlying commutative-ring presentation
as the derived functors, avoiding repeated conversion of the inverse-limit ring.
The shared inverse-limit definition is unchanged. Scalar-unit sections use
the existing restriction-section identity. The finite counit and gamma supply
their existing isomorphism proofs explicitly. A generic constructor packages the
two localization isomorphisms and the invertible counit; both model constructors
use it. The two global comparison definitions retain their complete source bodies. Three
generic equation constructors and three coefficient tensor-model constructors
package the original predicate equations inside this item. Two generic complex-transformation interfaces display iterated complex functors
while retaining the original mapped natural transformations. The unique-comparison
selector retains the exact choice term from each existing unique-existence theorem.
Every selection retains its original normalized term; the added generic selector
takes a unique-existence proof. The tensor-model
constructors apply the existing `CoefficientTensorModels.iso` to the original
fields; they are new declarations, not aliases inserted into any structure. The
shared total-tensor body and the published structure fields are unchanged.
The scalar-section model names its sections functor separately at each level, with
the recorded source category and its additive zero-map proof explicit. These are the
same objects, maps and equations, without changing any hypothesis or conclusion.

No target statement or source-library module changes. The normal target-definition
review applies wherever a target statement uses these definitions; the canonical
body equalities establish unchanged objects, maps and equations. No other group's
module is adapted. The two original open theorems remain unchanged; this packet repairs the
returned definitions and interfaces without adding holes.

The local inference-size bound is 128. Let cleanup is disabled only for the
scalar-sections model, avoiding a redundant transformation of its named functor.
The additivity instance now uses the existing proved
`scalarReductionExtensionAdditive` with exactly its original type and priority.
Neither change affects exported attributes or any mathematical contract.

## Old

`WeilConjectures.coefficientTowerSections`:

```lean
noncomputable def coefficientTowerSections :
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) :=
  (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l E W)
    AddCommGrpCat.{max u (t+1)}).obj
      (preadditiveCoyoneda.obj (op (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E W))))
```

`WeilConjectures.coefficientFiniteQuotientModel`:

```lean
noncomputable def coefficientFiniteQuotientModel {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P) :
    (coefficientFiniteQuotientDerived l E W h).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  letI := coefficientFiniteQuotientCounit_isIso l E W h P hP
  (coefficientFiniteQuotientDerived l E W h).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((coefficientFiniteQuotientCounit l E W h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _
```

`WeilConjectures.coefficientOrdinaryQuotientComponent`:

```lean
noncomputable def coefficientOrdinaryQuotientComponent {m n : ℕ} (h : n ≤ m)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj M) :=
  (coefficientQuotientNatTrans
    (scalarReductionExtension_adjunction l E W m).choose
    (scalarReductionExtension_adjunction l E W n).choose
    (normalizedDVRModuleRes l E W h)
    (eqToIso (coefficientRestrictionComp l E W h))).app M
```

`WeilConjectures.coefficientIntegralScalarUnitSection`:

```lean
noncomputable def coefficientIntegralScalarUnitSection (n : ℕ)
    (M : scalarReductionSource l E W) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((scalarReductionExtension l E W n).obj M).val.obj V :=
  (((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app V x)
```

`WeilConjectures.coefficientFiniteReductionModel`:

```lean
noncomputable def coefficientFiniteReductionModel
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (coefficientFiniteDerivedExtension l E W n).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  letI : IsIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q)) :=
    coefficientFiniteReductionCounit_isIso l E W Q hQ n
  (coefficientFiniteDerivedExtension l E W n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app Q).symm ≪≫
    asIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _
```

`WeilConjectures.CoefficientDerivedSystemCalculus.gamma`:

```lean
noncomputable def CoefficientDerivedSystemCalculus.gamma
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    (coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientSequenceLimit l E W).obj N) ≅
      coefficientMappingLimit.{max u (t+1)}.obj
        ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) :=
  letI := S.enriched_isIso P N hN
  (coefficientIntegralSections l E W).mapIso
      (asIso (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
        S.adjunction S.reductionTensor P N)) ≪≫
    S.globalLimit.app
      ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))
```

`WeilConjectures.CoefficientScalarSectionsModel`:

```lean
def CoefficientScalarSectionsModel
    (D : CoefficientDerivedSystemScalarData l E W) : Prop :=
  ∀ (n : ℕ) (I : CochainComplex (scalarReductionTarget l E W n) ℤ),
    coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (((scalarReductionRestriction l E W n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫
      (coefficientIntegralSections l E W).map
          ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I) ≫
      (D.scalarSections n).hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (D.ordinaryScalarSections n).hom
      (ComplexShape.up ℤ)).app I) ≫
      coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) I
```

`WeilConjectures.CoefficientReductionModels`:

```lean
def CoefficientReductionModels
    (R : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (ρ : ∀ n : ℕ, R ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (e : R.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q),
      (∀ n : ℕ,
        (coefficientSequenceDerivedEvaluation l E W n).map e.hom ≫
          (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (κ n).hom =
        (ρ n).hom.app (DerivedCategory.Q.obj Q) ≫
          (coefficientFiniteReductionModel l E W Q hQ n).hom) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
            (ComplexShape.up ℤ)).app C ≫
          ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (κ n).hom =
        (κ m).hom ≫ (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
          (ComplexShape.up ℤ)).app Q)
```

`WeilConjectures.CoefficientReductionPresentation`:

```lean
def CoefficientReductionPresentation
    (S : CoefficientDerivedSystemReduction l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :
    Prop :=
  (∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E W n).map e.hom ≫
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C ≫
      DerivedCategory.Q.map (κ n).hom =
    (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
      (coefficientFiniteReductionModel l E W P hP n).hom) ∧
  (∀ (m n : ℕ) (h : n ≤ m),
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (ComplexShape.up ℤ)).app C ≫
      ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (κ n).hom =
    (κ m).hom ≫ (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
      (ComplexShape.up ℤ)).app P)
```

`WeilConjectures.CoefficientFiniteQuotientTensorNormalization`:

```lean
def CoefficientFiniteQuotientTensorNormalization (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) Q),
    ∃ e : ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      CoefficientScalarTensorGenerators.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
        (coefficientFiniteQuotientExtension l E W h)
        (hF := coefficientFiniteQuotientExtensionAdditive l E W h)
        (coefficientFiniteQuotientUnitSection l E W h) P Q e ∧
      (coefficientFiniteQuotientDerived l E W h).map
          (((S.finiteTensorModel m).iso (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m) (S.finiteClosed m) P Q hP hQ).hom) ≫
        (D.tensor h).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (S.finiteClosed n).tensor.map
          (Prod.mkHom (coefficientFiniteQuotientModel l E W h P hP).hom
            (coefficientFiniteQuotientModel l E W h Q hQ).hom) =
      (coefficientFiniteQuotientModel l E W h _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W m) P Q hP hQ)).hom ≫
        DerivedCategory.Q.map e.hom ≫
        ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n) _ _
          (D.preservesKFlat h P hP) (D.preservesKFlat h Q hQ)).hom
```

`WeilConjectures.CoefficientFiniteTensorNormalization`:

```lean
def CoefficientFiniteTensorNormalization (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (coefficientFiniteDerivedExtension l E W n).map
      ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed P Q hP hQ).hom) ≫
      (S.finiteTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom (coefficientFiniteReductionModel l E W P hP n).hom
          (coefficientFiniteReductionModel l E W Q hQ n).hom) =
    (coefficientFiniteReductionModel l E W _
      (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) n).hom ≫
      DerivedCategory.Q.map (coefficientScalarTensorIso l E W n P Q).hom ≫
      ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n) _ _
        ((coefficientTensorModelPreservation l E W).1 P hP n)
        ((coefficientTensorModelPreservation l E W).1 Q hQ n)).hom
```

`WeilConjectures.CoefficientEvaluationTensorNormalization`:

```lean
def CoefficientEvaluationTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q),
    (coefficientSequenceDerivedEvaluation l E W n).map
      ((S.systemTensorModel.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) S.systemClosed P Q hP hQ).hom) ≫
      (S.evaluationTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P)
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app Q)) =
    (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n P Q).hom ≫
      ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n) _ _
        ((coefficientTensorModelPreservation l E W).2 P hP n)
        ((coefficientTensorModelPreservation l E W).2 Q hQ n)).hom
```

`WeilConjectures.CoefficientReductionTensorNormalization`:

```lean
def CoefficientReductionTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) →
    ∃ (C D Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
      (eD : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj D)
      (eZ : S.reduction.obj (DerivedCategory.Q.obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))) ≅
        DerivedCategory.Q.obj Z)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          D ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q)
      (κZ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          Z ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)))
      (ψ : Z ⟶ (coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (C, D)),
      CoefficientReductionPresentation l E W S P hP C eC κC ∧
      CoefficientReductionPresentation l E W S Q hQ D eD κD ∧
      CoefficientReductionPresentation l E W S _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) Z eZ κZ ∧
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ψ ≫ (coefficientEvaluationTensorIso l E W n C D).hom ≫
          (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
              (Prod.mkHom (κC n).hom (κD n).hom) =
        (κZ n).hom ≫ (coefficientScalarTensorIso l E W n P Q).hom) ∧
      S.reduction.map ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed P Q hP hQ).hom) ≫
        S.reductionTensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom) =
      eZ.hom ≫ DerivedCategory.Q.map ψ ≫
        (S.systemTensorModel.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) S.systemClosed C D hC hD).hom
```

`WeilConjectures.CoefficientGlobalLimitModel`:

```lean
def CoefficientGlobalLimitModel (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      (coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)) ≫
      S.globalLimit.hom.app (DerivedCategory.Q.obj K) =
    coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      coefficientMappingLimit.{max u (t+1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K))
```

`WeilConjectures.CoefficientReductionTensorEvaluation`:

```lean
def CoefficientReductionTensorEvaluation (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (S.reductionTensor.hom.app (P, Q)) ≫
      (S.evaluationTensor n).hom.app (S.reduction.obj P, S.reduction.obj Q) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom ((S.reductionEvaluation n).hom.app P)
          ((S.reductionEvaluation n).hom.app Q)) =
    (S.reductionEvaluation n).hom.app (S.integralClosed.tensor.obj (P, Q)) ≫
      (S.finiteTensor n).hom.app (P, Q)
```

`WeilConjectures.coefficientScalarTensorIso`:

```lean
noncomputable def coefficientScalarTensorIso (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :=
  (coefficientScalarTensorIso_exists l E W n P Q).choose
```

`WeilConjectures.coefficientEvaluationTensorIso`:

```lean
noncomputable def coefficientEvaluationTensorIso (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  (coefficientEvaluationTensorIso_exists l E W n P Q).choose
```

## New

`WeilConjectures.coefficientTowerSections`:

```lean
noncomputable def coefficientTowerSections :
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) :=
  (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l E W)
    AddCommGrpCat.{max u (t+1)}).obj
      (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W))
```

`WeilConjectures.coefficientFiniteQuotientModel`:

```lean
noncomputable def coefficientFiniteQuotientModel {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P) :
    (coefficientFiniteQuotientDerived l E W h).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  coefficientLocalizedCounitModel (coefficientFiniteQuotientDerived l E W h) P
    (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex (.up ℤ)).obj P)
    ((coefficientFiniteQuotientCounit l E W h).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    (coefficientFiniteQuotientCounit_isIso l E W h P hP)
```

`WeilConjectures.coefficientOrdinaryQuotientComponent`:

```lean
noncomputable def coefficientOrdinaryQuotientComponent {m n : ℕ} (h : n ≤ m)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj M) :=
  (coefficientOrdinaryQuotientNaturalTransformation l E W h).app M
```

`WeilConjectures.coefficientIntegralScalarUnitSection`:

```lean
noncomputable def coefficientIntegralScalarUnitSection (n : ℕ)
    (M : scalarReductionSource l E W) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((scalarReductionExtension l E W n).obj M).val.obj V :=
  coefficientRestrictionSection
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    ((scalarReductionExtension l E W n).obj M) V
    (((coefficientOrdinaryScalarAdjunction l E W n).unit.app M).val.app V x)
```

`WeilConjectures.coefficientFiniteReductionModel`:

```lean
noncomputable def coefficientFiniteReductionModel
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (coefficientFiniteDerivedExtension l E W n).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  coefficientLocalizedCounitModel (coefficientFiniteDerivedExtension l E W n) Q
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
    ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))
    (coefficientFiniteReductionCounit_isIso l E W Q hQ n)
```

`WeilConjectures.CoefficientDerivedSystemCalculus.gamma`:

```lean
noncomputable def CoefficientDerivedSystemCalculus.gamma
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    (coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientSequenceLimit l E W).obj N) ≅
      coefficientMappingLimit.{max u (t+1)}.obj
        ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) :=
  (coefficientIntegralSections l E W).mapIso
      (@asIso _ _ _ _
        (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
          S.adjunction S.reductionTensor P N) (S.enriched_isIso P N hN)) ≪≫
    S.globalLimit.app
      ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))
```

`WeilConjectures.CoefficientScalarSectionsModel`:

```lean
def CoefficientScalarSectionsModel
    (D : CoefficientDerivedSystemScalarData l E W) : Prop :=
  ∀ (n : ℕ) (I : CochainComplex (scalarReductionTarget l E W n) ℤ),
    let G : scalarReductionTarget l E W n ⥤ AddCommGrpCat.{max u (t+1)} :=
      coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
    let : G.PreservesZeroMorphisms := by
      let : G.Additive := CategoryTheory.additive_coyonedaObj' _
      exact Functor.preservesZeroMorphisms_of_additive G
    CoefficientComparisonEquation
      (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (((scalarReductionRestriction l E W n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))
      ((coefficientIntegralSections l E W).map
          ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I))
      ((D.scalarSections n).hom.app (DerivedCategory.Q.obj I))
      (DerivedCategory.Q.map
      (coefficientComplexCompositeSourceTransformation
        (scalarReductionRestriction l E W n)
        (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W))
        (H := G) (D.ordinaryScalarSections n).hom I))
      (coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) I)
```

`WeilConjectures.CoefficientReductionModels`:

```lean
def CoefficientReductionModels
    (R : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (ρ : ∀ n : ℕ, R ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (e : R.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q),
      (∀ n : ℕ,
        CoefficientComparisonEquation
          ((coefficientSequenceDerivedEvaluation l E W n).map e.hom)
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C)
          (DerivedCategory.Q.map (κ n).hom)
          ((ρ n).hom.app (DerivedCategory.Q.obj Q))
          ((coefficientFiniteReductionModel l E W Q hQ n).hom)) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        CoefficientTransitionEquation
          (coefficientComplexCompositeTransformation
            (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
            (coefficientSequenceTransition l E W h) C)
          (((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (κ n).hom)
          ((κ m).hom)
          (coefficientComplexCompositeTransformation
            (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
            (coefficientOrdinaryQuotient l E W h) Q))
```

`WeilConjectures.CoefficientReductionPresentation`:

```lean
def CoefficientReductionPresentation
    (S : CoefficientDerivedSystemReduction l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :
    Prop :=
  (∀ n : ℕ,
    CoefficientComparisonEquation
      ((coefficientSequenceDerivedEvaluation l E W n).map e.hom)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C)
      (DerivedCategory.Q.map (κ n).hom)
      ((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P))
      ((coefficientFiniteReductionModel l E W P hP n).hom)) ∧
  (∀ (m n : ℕ) (h : n ≤ m),
    CoefficientTransitionEquation
      (coefficientComplexCompositeTransformation
        (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientSequenceTransition l E W h) C)
      (((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (κ n).hom)
      ((κ m).hom)
      (coefficientComplexCompositeTransformation
        (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientOrdinaryQuotient l E W h) P))
```

`WeilConjectures.CoefficientFiniteQuotientTensorNormalization`:

```lean
def CoefficientFiniteQuotientTensorNormalization (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) Q),
    ∃ e : ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m)).obj ((P), (Q)))) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      CoefficientScalarTensorGenerators.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
        (coefficientFiniteQuotientExtension l E W h)
        (hF := coefficientFiniteQuotientExtensionAdditive l E W h)
        (coefficientFiniteQuotientUnitSection l E W h) P Q e ∧
      CoefficientTensorComparisonSquare (S.finiteClosed m).tensor
        (S.finiteClosed n).tensor (coefficientFiniteQuotientDerived l E W h) DerivedCategory.Q
        (coefficientFiniteTensorModelIso l E W S m P Q hP hQ).hom
        (D.tensor h).hom
        (coefficientFiniteQuotientModel l E W h P hP).hom
        (coefficientFiniteQuotientModel l E W h Q hQ).hom
        (coefficientFiniteQuotientModel l E W h _
          (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m) P Q hP hQ)).hom e.hom
        (coefficientFiniteTensorModelIso l E W S n _ _
          (D.preservesKFlat h P hP) (D.preservesKFlat h Q hQ)).hom
```

`WeilConjectures.CoefficientFiniteTensorNormalization`:

```lean
def CoefficientFiniteTensorNormalization (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    CoefficientTensorComparisonSquare S.integralClosed.tensor (S.finiteClosed n).tensor
      (coefficientFiniteDerivedExtension l E W n) DerivedCategory.Q
      (coefficientIntegralTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors P Q hP hQ).hom
      (S.finiteTensor n).hom
      (coefficientFiniteReductionModel l E W P hP n).hom
      (coefficientFiniteReductionModel l E W Q hQ n).hom
      (coefficientFiniteReductionModel l E W _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) n).hom
      (coefficientScalarTensorIso l E W n P Q).hom
      (coefficientFiniteTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors n _ _
        ((coefficientTensorModelPreservation l E W).1 P hP n)
        ((coefficientTensorModelPreservation l E W).1 Q hQ n)).hom
```

`WeilConjectures.CoefficientEvaluationTensorNormalization`:

```lean
def CoefficientEvaluationTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q),
    CoefficientTensorComparisonSquare S.systemClosed.tensor (S.finiteClosed n).tensor
      (coefficientSequenceDerivedEvaluation l E W n) DerivedCategory.Q
      (coefficientSystemTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors P Q hP hQ).hom
      (S.evaluationTensor n).hom
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app Q)
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app _)
      (coefficientEvaluationTensorIso l E W n P Q).hom
      (coefficientFiniteTensorModelIso l E W
        S.toCoefficientDerivedSystemTensors n _ _
        ((coefficientTensorModelPreservation l E W).2 P hP n)
        ((coefficientTensorModelPreservation l E W).2 Q hQ n)).hom
```

`WeilConjectures.CoefficientReductionTensorNormalization`:

```lean
def CoefficientReductionTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) →
    ∃ (C D Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
      (eD : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj D)
      (eZ : S.reduction.obj (DerivedCategory.Q.obj
        (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj ((P), (Q))))) ≅
        DerivedCategory.Q.obj Z)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          D ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q)
      (κZ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          Z ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj ((P), (Q)))))
      (ψ : Z ⟶ (coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (C, D)),
      CoefficientReductionPresentation l E W S P hP C eC κC ∧
      CoefficientReductionPresentation l E W S Q hQ D eD κD ∧
      CoefficientReductionPresentation l E W S _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) Z eZ κZ ∧
      (∀ n : ℕ,
        CoefficientComparisonEquation
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ)
          (coefficientEvaluationTensorIso l E W n C D).hom
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
              (Prod.mkHom (κC n).hom (κD n).hom))
          (κZ n).hom (coefficientScalarTensorIso l E W n P Q).hom) ∧
      CoefficientTensorComparisonSquare S.integralClosed.tensor S.systemClosed.tensor
        S.reduction DerivedCategory.Q
        (coefficientIntegralTensorModelIso l E W
          S.toCoefficientDerivedSystemTensors P Q hP hQ).hom
        S.reductionTensor.hom eC.hom eD.hom eZ.hom ψ
        (coefficientSystemTensorModelIso l E W
          S.toCoefficientDerivedSystemTensors C D hC hD).hom
```

`WeilConjectures.CoefficientGlobalLimitModel`:

```lean
def CoefficientGlobalLimitModel (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CoefficientComparisonEquation
      (coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      ((coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
      (S.globalLimit.hom.app (DerivedCategory.Q.obj K))
      (coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      (coefficientMappingLimit.{max u (t+1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
```

`WeilConjectures.CoefficientReductionTensorEvaluation`:

```lean
def CoefficientReductionTensorEvaluation (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    CoefficientComparisonEquation
      ((coefficientSequenceDerivedEvaluation l E W n).map
        (S.reductionTensor.hom.app (P, Q)))
      ((S.evaluationTensor n).hom.app (S.reduction.obj P, S.reduction.obj Q))
      ((S.finiteClosed n).tensor.map
        (Prod.mkHom ((S.reductionEvaluation n).hom.app P)
          ((S.reductionEvaluation n).hom.app Q)))
      ((S.reductionEvaluation n).hom.app (S.integralClosed.tensor.obj (P, Q)))
      ((S.finiteTensor n).hom.app (P, Q))
```

`WeilConjectures.coefficientScalarTensorIso`:

```lean
noncomputable def coefficientScalarTensorIso (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :=
  coefficientUniqueComparisonChoice (coefficientScalarTensorIso_exists l E W n P Q)
```

`WeilConjectures.coefficientEvaluationTensorIso`:

```lean
noncomputable def coefficientEvaluationTensorIso (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  coefficientUniqueComparisonChoice (coefficientEvaluationTensorIso_exists l E W n P Q)
```

The twelve new public definitions name the existing ordinary adjunction, quotient
transformation, canonical localized counit, three generic comparison equations,
three coefficient tensor-model isomorphisms, two complex transformations and the
original unique-comparison choice. Their sources and complete bodies
follow; all are attached to the existing DAG node.
Local instance and reducibility settings add no fields or assumptions.

`WeilConjectures.CoefficientComparisonEquation`:

```lean
def CoefficientComparisonEquation
    {D : Type a} [Category.{b} D] {X₀ X₁ X₂ X₃ X₄ : D}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₄)
    (p : X₀ ⟶ X₃) (q : X₃ ⟶ X₄) : Prop := f ≫ g ≫ h = p ≫ q
```

`WeilConjectures.CoefficientTensorComparisonSquare`:

```lean
def CoefficientTensorComparisonSquare
    {A : Type a} {B : Type b} {K : Type c}
    [Category.{v} A] [Category.{w} B] [Category.{r} K]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (F : A ⥤ B) (Q : K ⥤ B)
    {X Y Z : A} {X' Y' Z' N : K}
    (s : Z ⟶ T.obj (X, Y)) (μ : T ⋙ F ⟶ F.prod F ⋙ T')
    (p : F.obj X ⟶ Q.obj X') (q : F.obj Y ⟶ Q.obj Y')
    (z : F.obj Z ⟶ Q.obj Z') (e : Z' ⟶ N)
    (t : Q.obj N ⟶ T'.obj (Q.obj X', Q.obj Y')) : Prop :=
  F.map s ≫ μ.app (X, Y) ≫ T'.map (Prod.mkHom p q) = z ≫ Q.map e ≫ t
```

`WeilConjectures.CoefficientTransitionEquation`:

```lean
def CoefficientTransitionEquation
    {D : Type a} [Category.{b} D] {X₀ X₁ X₂ X₃ : D}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₃) (p : X₀ ⟶ X₂) (q : X₂ ⟶ X₃) : Prop :=
  f ≫ g = p ≫ q
```

`WeilConjectures.coefficientComplexCompositeSourceTransformation`:

```lean
noncomputable def coefficientComplexCompositeSourceTransformation
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{v} A] [HasZeroMorphisms A]
    [Category.{w} B] [HasZeroMorphisms B]
    [Category.{r} D] [HasZeroMorphisms D]
    (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (G : B ⥤ D) [G.PreservesZeroMorphisms]
    {H : A ⥤ D} [H.PreservesZeroMorphisms] (τ : F ⋙ G ⟶ H)
    (P : CochainComplex A ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (H.mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P
```

`WeilConjectures.coefficientComplexCompositeTransformation`:

```lean
noncomputable def coefficientComplexCompositeTransformation
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{v} A] [HasZeroMorphisms A]
    [Category.{w} B] [HasZeroMorphisms B]
    [Category.{r} D] [HasZeroMorphisms D]
    (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (G : B ⥤ D) [G.PreservesZeroMorphisms]
    {H : A ⥤ D} [H.PreservesZeroMorphisms] (τ : H ⟶ F ⋙ G)
    (P : CochainComplex A ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P
```

`WeilConjectures.coefficientFiniteTensorModelIso`:

```lean
noncomputable def coefficientFiniteTensorModelIso
    (S : CoefficientDerivedSystemTensors l E W) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n) Q) :
    DerivedCategory.Q.obj (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).obj ((P), (Q)))) ≅
      (S.finiteClosed n).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
    (S.finiteTensorModel n) P Q hP hQ
```

`WeilConjectures.coefficientIntegralTensorModelIso`:

```lean
noncomputable def coefficientIntegralTensorModelIso
    (S : CoefficientDerivedSystemTensors l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q) :
    DerivedCategory.Q.obj (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj ((P), (Q)))) ≅
      S.integralClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed
    S.integralTensorModel P Q hP hQ
```

`WeilConjectures.coefficientLocalizedCounitModel`:

```lean
noncomputable def coefficientLocalizedCounitModel
    {A : Type a} {B : Type b} [Category.{v} A] [Abelian A]
    [Category.{w} B] [Abelian B]
    [HasDerivedCategory.{r} A] [HasDerivedCategory.{c} B]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    (f : F.obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj Q))
    (hf : IsIso f) : F.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj Q :=
  F.mapIso ((DerivedCategory.quotientCompQhIso A).app P).symm ≪≫
    @asIso _ _ _ _ f hf ≪≫ (DerivedCategory.quotientCompQhIso B).app Q
```

`WeilConjectures.coefficientOrdinaryQuotientNaturalTransformation`:

```lean
noncomputable def coefficientOrdinaryQuotientNaturalTransformation {m n : ℕ} (h : n ≤ m) :
    scalarReductionExtension l E W m ⟶
      scalarReductionExtension l E W n ⋙ normalizedDVRModuleRes l E W h :=
  coefficientQuotientNatTrans
    (coefficientOrdinaryScalarAdjunction l E W m)
    (coefficientOrdinaryScalarAdjunction l E W n)
    (normalizedDVRModuleRes l E W h) (eqToIso (coefficientRestrictionComp l E W h))
```

`WeilConjectures.coefficientOrdinaryScalarAdjunction`:

```lean
noncomputable def coefficientOrdinaryScalarAdjunction (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose
```

`WeilConjectures.coefficientSystemTensorModelIso`:

```lean
noncomputable def coefficientSystemTensorModelIso
    (S : CoefficientDerivedSystemTensors l E W)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q) :
    DerivedCategory.Q.obj (((coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology
      (Scheme.ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)).obj ((P), (Q)))) ≅
      S.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CoefficientTensorModels.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel P Q hP hQ
```

`WeilConjectures.coefficientUniqueComparisonChoice`:

```lean
noncomputable def coefficientUniqueComparisonChoice
    {α : Sort a} {p : α → Prop} (h : ∃! x, p x) : α := h.choose
```

## Users

The table covers the seventeen changed bodies and all current direct importers.
A fresh read-only source scan follows the current import graph, strips comments,
and matches whole-word final declaration names as `tools/downstream.py --uses`
does. Retaining string contents can only over-approximate the uses. This avoids
writing the shared repository's source-index cache. There are 384 users, including
105 current direct importers. Every named use
retains the same mathematical meaning. Fresh direct-importer compilation is
recorded in the report; this record does not assert a passing build in advance.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Algebra.Homology.ScalarHomComparisonTower` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Algebra.Homology.ScalarHomDerivedSquareCoherence` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.CategoryTheory.CompactSupportIdentityCalculus` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AffineSpaceZeroSectionConstructions` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AllStageCtfPullbackUnit` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.AugmentedReductionNaturality` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CanonicalOpenRestrictionModel` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.CanonicalTateScalarComparisons` | unclaimed | Same `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.CartierRelativeKummerRealization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ClassicalRawLissePointFibres` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ClosedSectionCompactOriginData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ClosedTestScalarComparisonMaps` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ClosedTestScalarModelDiagrams` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ClosedTestScalarSectionSquares` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | J6 (assigned repair) | Same `CoefficientDerivedSystemCalculus.gamma`, `CoefficientEvaluationTensorNormalization`, `CoefficientFiniteQuotientTensorNormalization`, `CoefficientFiniteTensorNormalization`, `CoefficientGlobalLimitModel`, `CoefficientReductionModels`, `CoefficientReductionPresentation`, `CoefficientReductionTensorEvaluation`, `CoefficientReductionTensorNormalization`, `CoefficientScalarSectionsModel`, `coefficientEvaluationTensorIso`, `coefficientFiniteQuotientModel`, `coefficientFiniteReductionModel`, `coefficientIntegralScalarUnitSection`, `coefficientOrdinaryQuotientComponent`, `coefficientScalarTensorIso`, `coefficientTowerSections`; no source adaptation. |
| `Sheaf.Paper.CoefOpenTensorEvaluationData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CoefSupportOpenTensorModel` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CoefficientEnrichedGlobalShift` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`, `coefficientTowerSections`; no source adaptation. |
| `Sheaf.Paper.CoefficientEvaluationNaturality` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionAssociationQuotientUnits` | unclaimed | Same `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionAssociationScalarUnits` | unclaimed | Same `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionAssociationSuccessor` | unclaimed | Same `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionAssociationTensorCoordinates` | unclaimed | Same `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionOrdinaryQuotientIso` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionReductionData` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionStrictDerivedComparison` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionStrictTensorNormalized` | unclaimed | Same `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.CoefficientReductionNaturalCochainComparison` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CoherentPrimitiveReductionPresentation` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CoherentQuotientReductionComparison` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.CommonTensorComparisonDescent` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CommonTensorComparisonRepresentatives` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientTransition` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | G1 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompactSupportNativeSystemEvaluation` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedScalarDescent` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedTowerLimit` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompactSupportProjectionCoefficientChange` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompactSupportRealizationCoordinates` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorization` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarRefinement` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompactSupportSystemTransposeNormalization` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealizationData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.CompletedComparisonQuotientNormalization` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.CompletedComparisonQuotientRealization` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.CompletedHomScalarTranspose` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompletedOpenTensorRepresentatives` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | K2 | Same `CoefficientReductionPresentation`, `coefficientEvaluationTensorIso`; no source adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | B4 | Same `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | N4 | Same `coefficientEvaluationTensorIso`; no source adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CompletionUnitDerivedAdjunctionComparison` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CompletionUnitFiniteMateComparison` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CompletionUnitFixedCalculusModels` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CompletionUnitModels` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.CompositeProjectionCoefficients` | K4 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CondensedCompactSupportProjection` | J2 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CondensedCompositorRealization` | D3 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCompositorData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CoordinateTowerNormalizationData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.CoordinateTowerNormalizationInduction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.DerivedHomSubstitutionCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | C4 | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.EffectiveCompletionPresentationModels` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.EffectiveQuotientModelDescent` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ExactProperOpenProjectionMate` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | K3 | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FdCompletedCompositorNormalization` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.FdPullbackComparison` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralComparisons` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralModels` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FieldExtensionRationalComparisons` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FieldExtensionRationalModels` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FieldPurityTransposeArrows` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteCounitRestrictionTowers` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.FiniteExceptionalSiteNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteOpenGammaRestriction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteOpenProductOperations` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteOpenProductSwap` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteOrientationReduction` | M3 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeTransposes` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FinitePurityCounitSystem` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteQuotientPullbackDescent` | unclaimed | Same `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.FiniteRationalDerivedOperations` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.FiniteRestrictionConstructibleVertices` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.FiniteRestrictionDiagramNaturality` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Same `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.FrameworkPbcPullbackComparisonData` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.FreeParameterEvaluationCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.GaloisKInjectiveSectionModel` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.GeometricCondensedFiniteScalarModel` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IdentityCompactificationLimitComparisons` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralCoherenceData` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralComparisonSystemData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.IntegralFiniteScalarModelDefinitions` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralFiniteScalarPerfectModel` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonRealization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralGoodQuotientPresentation` | unclaimed | Same `coefficientEvaluationTensorIso`; no source adaptation. |
| `Sheaf.Paper.IntegralImmersionPullbackNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralImmersionPullbackNormalizationData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralImmersionShiftCompatibility` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralMappingLimitProjections` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralOperationRoosEffectivity` | unclaimed | Same `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarComparisonModels` | J1 | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | E1 | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralOrientedExchangeSquares` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralProjectionSystemCoordinates` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparisonData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackCounitProjection` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralStratumChartRestrictionsData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.IntegralStrictReductionModel` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | Same `coefficientEvaluationTensorIso`; no source adaptation. |
| `Sheaf.Paper.IntegrationTransposeScalarMate` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.InternalSectionHomComparisonData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.InternalSectionHomContinuityComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.InternalSectionScalarHomTransportData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.IteratedPurityScalarPasting` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.KummerSuccessiveDescent` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NativeCompactProjectionFormula` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NativeCompactSupportFiniteComparison` | P4 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NativeOpenDerivedTensor` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.NormalizedArithmeticInterpolation` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTrace` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTraceData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.OpenRestrictionAugmentedDescent` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.OpenRestrictionCounitOnGoodComplexes` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.OrientationPerfectLines` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.OrientedDoubleHomCancellation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.OrientedPerfectDuality` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.PodCompletionReindexModels` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PodCompletionUnitScalarIntertwining` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PodReconstructionCommonStageData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PodReconstructionRawRationalNaturality` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorScalar` | unclaimed | Same `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.PointSystemInsertionComposition` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PointSystemInsertionData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PointSystemNormalizedComparisonData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PointSystemTransportDescent` | D4 | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PrimitiveQuotientRealizationComparisons` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientEvaluationTensorIso`; no source adaptation. |
| `Sheaf.Paper.ProductOpenCounitNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjection` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjectionData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ProjectionScalarSquare` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ProperIntegralTowerComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PullbackCommonStrictTowerModels` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.PurReductionFiniteShiftNormalization` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurReductionLimitShiftData` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurSequenceAdjointResolutionData` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.PurSequenceAdjointResolutionShifts` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurSequenceKFlatComparisonData` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurSequenceKFlatComparisonShifts` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurSequenceOrdinaryFactorization` | unclaimed | Same `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.PurSequenceReductionShifts` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurSequenceReductionUniversal` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionGamma` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.QuotientCompletedCompositorUnit` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.QuotientExpressionKFlatModels` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | unclaimed | Same `coefficientEvaluationTensorIso`, `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.QuotientExpressionKFlatOperations` | unclaimed | Same `coefficientEvaluationTensorIso`, `coefficientFiniteQuotientModel`, `coefficientOrdinaryQuotientComponent`; no source adaptation. |
| `Sheaf.Paper.QuotientExpressionStrictKFlatTowers` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RationalPurityExchangeEndpointData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RationalPurityExchangeEndpoints` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RationalPurityLocalizedFamilyData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.RingedRestrictionStrictLimitCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.ScalarPullTensorCoefficientCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SectionCompactSourceMaps` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SectionSupportedComparisonIso` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SectionSupportedProExchangeIso` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.SequenceKInjectiveComparisonShifts` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.SfAdicCommonStageDescentEquivalence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SfAmbientIntegralDirectImage` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.SfFieldMateDomain` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.SixFunctorOrientationFiniteFamily` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | H2 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothOrientationPuritySquares` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SpecifiedIntegralUnitOrientation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.StrictDirectImageMixedUnitData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.StrictLineHeartAssembly` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.StrictQuotientExpressions` | unclaimed | Same `coefficientEvaluationTensorIso`, `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.StrictReductionPresentationMap` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.StrictRefinementRestrictionSquares` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.StrictRefinementSeedRestriction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.StrictTensorAdjointConstructor` | unclaimed | Same `coefficientEvaluationTensorIso`, `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.StrictTensorOrdinaryAdjunct` | unclaimed | Same `coefficientEvaluationTensorIso`, `coefficientFiniteQuotientModel`; no source adaptation. |
| `Sheaf.Paper.SupportedCoefficientHomNaturality` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SupportedRootScalarSiteComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemCompatibleCompositorData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemCompatibleCompositorNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemCompositorRefinementSquare` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemInternalHomRepresentability` | unclaimed | Same `coefficientTowerSections`; no source adaptation. |
| `Sheaf.Paper.SystemProjectionChangeCompatibility` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaMaps` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemProjectionTriangleCompatibility` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemProperOpenInvertibility` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemRefinementConstructibleDomain` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemScalarProjectionData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.SystemScalarTransitionComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TowerGeometricPurityAssembly` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TowerGeometricPurityData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TowerPurityRealizedData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`, `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.Paper.TransportIntegralCounitData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TransportIntegralCounitRealization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionData` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.Paper.TwoOpenTensorChainNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.WeilCompactStructureTensorComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.WeilEquivarianceOfPurityAndTrace` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.WeilPurityEquivarianceData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.Paper.ZlFiniteIntegralFibreReconstruction` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineFormulaData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientation` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SecSmoothPurity.TransportFamily` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenCalculus` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.AugmentedStrictIntegralCompletion` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.CoefFinitePairingEvaluationData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.CoefSystemProjectionEvaluation` | unclaimed | Same `CoefficientReductionModels`; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairingData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Same `coefficientTowerSections`; no source adaptation. |
| `Sheaf.SixFunctors.FiniteOpenCartesianCalculus` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.FiniteReductionCompletionUnit` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalAmbientModels` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionDefinitions` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralOpenTensorRepresentative` | unclaimed | Same `coefficientFiniteReductionModel`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | C5 | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.KunnethFirstOpenSubstitution` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquareData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenExternalTensorNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherenceData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenFactorProjectionRealization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionData` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.OpenProjectionCompletedSquare` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRestrictionNormalization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletion` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletionData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenQuotientKoszulCompleteness` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.OpenQuotientKoszulModels` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.OpenSemilinearTensorModelData` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.SixFunctors.OpenStrictScalarTransport` | unclaimed | Same `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OpenTensorQuotientData` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.OrdinaryReductionAugmentedComputation` | unclaimed | Same `CoefficientReductionPresentation`, `coefficientIntegralScalarUnitSection`; no source adaptation. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementDescent` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ProjectionSystemCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionCounit` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionLocalTensor` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionWords` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.SemilinearOpenExternalCoherence` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenSupport` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.SystemTotalEnrichedTranspose` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.ThreeCellCompositor` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionNormalForm` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionSystemNormalForm` | unclaimed | Same `CoefficientDerivedSystemCalculus.gamma`; no source adaptation. |
| `Sheaf.TraceFormula.AutomorphismTensorReductionComparison` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | unclaimed | Original signatures retained; no source adaptation. |
| `Sheaf.TraceFormula.IsomorphismStrictQuotientModels` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | unclaimed | Same `CoefficientReductionPresentation`; no source adaptation. |

## Status

landed 20261027T050613-L-243522 2026-10-27 (merge of deliver/J6/Sheaf.Paper.CoefDerivedSystemEvaluationCalculus)
