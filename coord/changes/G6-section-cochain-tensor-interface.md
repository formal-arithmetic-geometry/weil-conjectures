# ResolutionConjugation.section_resolution_conjugation_identities

## Reason

Prove the assigned conjugation identities from their existing normalization,
representative and ordinary oplax comparisons, retaining the theorem signature verbatim.
The existing termwise functors expose large cochain constructions repeatedly during
kernel checking. retainedCochainFunctor stores their original object and map functions
as named fields, with their original functor laws; retainedCochainFunctor_eq is reflexivity.
The cochain equivalence and two termwise pullbacks use this definitionally identical
representation. The original monoidal structure on the section termwise pullback is
retained explicitly. No object, map, total, tensor, unit, differential, or coherence law changes.

Fifteen existing tensor caches move from SectionTotalOplaxComparisonData
into its publicly imported SectionCochainTensorComparison. Their names, types,
visibility, attributes, priorities and disabled-instance status stay the same.
Their blueprint links identify their new definition node.
The new canonical component interfaces expose the specified comparison maps and
prove their naturality and representative normalization, without adding holes or choices.
All current shared conjugation constructors and inverse laws remain present.

SectionModuleOperationsData.equivalence retains its body, type and reducible status;
only the abbreviation kernel hint changes. All original data bodies and attributes
in the current SectionDerivedTensorData remain unchanged, including the D7 component APIs,
regular single unit and direct-object total-functor representation landed during this session.
Both internalTotalTensor and totalTensor retain their original bodies and their original
inferred localization parameters explicitly. Three scoped linter exceptions document
these intentionally retained original parameters.
The assigned module’s component definitions use canonical types for the same maps,
including exactly the original regular units. Equations and substitution predicates
assert the same composites. Their meaning is subject to the normal independent review
for definitions used below the targets. No target signature or adopted source declaration changes.

## Old

`Sheaf.Paper.SectionModuleOperationsData.equivalence`:

```lean
abbrev equivalence (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)
```

`Sheaf.Paper.SectionDerivedTensorData.internalTotalTensor`:

```lean
def internalTotalTensor (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ × CochainComplex (internalModules Λ X) ℤ ⥤
      CochainComplex (internalModules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (internalModules Λ X))
```

`Sheaf.Paper.SectionDerivedTensorData.totalTensor`:

```lean
def totalTensor (X : Scheme.{u}) :
    CochainComplex (modules Λ X) ℤ × CochainComplex (modules Λ X) ℤ ⥤
      CochainComplex (modules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (modules Λ X))
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionOrdinaryMonoidal`:

```lean
instance totalSectionOrdinaryMonoidal (X : Scheme.{u}) :
    MonoidalCategory (modules Λ X) := inferInstance

-- Use the canonical ordinary structure when constructing the cochain caches below.
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalGraded`:

```lean
instance totalInternalGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionGraded`:

```lean
instance totalSectionGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalGoodLeft`:

```lean
instance totalInternalGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalGoodRight`:

```lean
instance totalInternalGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalTensorFour`:

```lean
instance totalInternalTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionGoodLeft`:

```lean
instance totalSectionGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionGoodRight`:

```lean
instance totalSectionGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionTensorFour`:

```lean
instance totalSectionTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalHasTensor`:

```lean
instance (priority := 4000) totalInternalHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionHasTensor`:

```lean
instance (priority := 4000) totalSectionHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (modules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalMonoidal`:

```lean
@[reducible] def totalInternalMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (internalModules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionMonoidal`:

```lean
@[reducible] def totalSectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (modules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalMonoidalStruct`:

```lean
@[reducible] def totalInternalMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (internalModules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionMonoidalStruct`:

```lean
@[reducible] def totalSectionMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (modules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalPull`:

```lean
@[reducible] def totalInternalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (internalModules Λ Y) ℤ ⥤ CochainComplex (internalModules Λ X) ℤ :=
  (CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionPull`:

```lean
@[reducible] def totalSectionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (modules Λ Y) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  (pullback Λ f).mapHomologicalComplex (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionEquivalence`:

```lean
@[reducible] def totalSectionEquivalence (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalTensorComparison`:

```lean
@[irreducible] def totalTensorComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (totalSectionEquivalence Λ X).obj (P ⊗ Q) ≅
      (totalSectionEquivalence Λ X).obj P ⊗ (totalSectionEquivalence Λ X).obj Q :=
  totalComparison Λ X P Q
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalUnitComparison`:

```lean
@[irreducible] def totalUnitComparison (X : Scheme.{u}) :
    (totalSectionEquivalence Λ X).obj (𝟙_ (CochainComplex (internalModules Λ X) ℤ)) ≅
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (equivalence Λ X).functor (.up ℤ) 0).app
      (𝟙_ (internalModules Λ X)) ≪≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).mapIso (ordinaryUnitComparison Λ X)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.actualInternalTotalUnit`:

```lean
@[irreducible] def actualInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalInternalPull Λ f).obj (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (internalModules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (CondensedRing.upperStar Λ f)
    (.up ℤ) 0).hom.app (𝟙_ (internalModules Λ Y)) ≫
    (HomologicalComplex.single (internalModules Λ X) (.up ℤ) 0).map
      (normalizationInternalUnit Λ f)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.sectionTotalUnit`:

```lean
@[irreducible] def sectionTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex (pullback Λ f) (.up ℤ) 0).hom.app
      (𝟙_ (modules Λ Y)) ≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).map (normalizationSectionUnit Λ f)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.conjugatedInternalTotalUnit`:

```lean
def conjugatedInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ⟶
      𝟙_ (CochainComplex (modules Λ X) ℤ) :=
  (totalSectionPull Λ f).map (totalUnitComparison Λ Y).inv ≫
    (termwisePullComparison Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))).inv ≫
    (totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
    (totalUnitComparison Λ X).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.eta`:

```lean
@[irreducible] def eta {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A) ⟶
      DerivedCategory.Q.obj ((totalInternalPull Λ f).obj A) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj A)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.epsilon`:

```lean
@[irreducible] def epsilon {X Y : Scheme.{u}} (f : X ⟶ Y) (P : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P) :=
  (pullback Λ f).mapDerivedCategoryFactors.hom.app P
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.d`:

```lean
@[irreducible] def d {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        (DerivedCategory.Q.obj ((totalInternalPull Λ f).obj A)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj A)) :=
  (sectionLocalizationComparison Λ X ((totalInternalPull Λ f).obj A)).hom ≫
    DerivedCategory.Q.map (termwisePullComparison Λ f A).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.j`:

```lean
@[irreducible] def j {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        ((internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A)) ⟶
      (derivedPullback Λ f).obj
        (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A)) :=
  (derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A) ≫
    (derivedPullback Λ f).map (sectionLocalizationComparison Λ Y A).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.dZ`:

```lean
@[irreducible] def dZ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        (DerivedCategory.Q.obj ((totalInternalPull Λ f).obj (A ⊗ B))) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj A ⊗ (totalSectionEquivalence Λ Y).obj B)) :=
  d Λ f (A ⊗ B) ≫
    DerivedCategory.Q.map ((totalSectionPull Λ f).map (totalComparison Λ Y A B).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.dOut`:

```lean
@[irreducible] def dOut {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedEquivalence Λ X).functor.obj (DerivedCategory.Q.obj
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)) ⟶
      DerivedCategory.Q.obj
        ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj A) ⊗
          (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj B)) :=
  (sectionLocalizationComparison Λ X
      ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)).hom ≫
    DerivedCategory.Q.map (totalComparison Λ X
      ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)).hom ≫
    DerivedCategory.Q.map
      ((termwisePullComparison Λ f A).hom ⊗ₘ (termwisePullComparison Λ f B).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.jTensor`:

```lean
@[irreducible] def jTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedEquivalence Λ X).functor.obj ((internalDerivedPullback Λ f).obj
        (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B)) ⟶
      (derivedPullback Λ f).obj ((tensor Λ Y).obj
        (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A),
          DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj B))) :=
  (derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B) ≫
    (derivedPullback Λ f).map
      ((tensorComparison Λ Y).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        (tensor Λ Y).map (Prod.mkHom (sectionLocalizationComparison Λ Y A).hom
          (sectionLocalizationComparison Λ Y B).hom))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.kTensor`:

```lean
@[irreducible] def kTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        ((internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A) ⊗
          (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj B)) ⟶
      (tensor Λ X).obj
        ((derivedPullback Λ f).obj
            (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A)),
          (derivedPullback Λ f).obj
            (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj B))) :=
  (tensorComparison Λ X).hom.app
      ((internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A),
        (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj B)) ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A))
      ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj B))) ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullback Λ f).map (sectionLocalizationComparison Λ Y A).hom)
      ((derivedPullback Λ f).map (sectionLocalizationComparison Λ Y B).hom))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.aInternal`:

```lean
@[irreducible] def aInternal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj ((totalInternalPull Λ f).obj (A ⊗ B)) :=
  (internalDerivedPullback Λ f).map
      (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := internalModules Λ Y)) A B) ≫
    eta Λ f (A ⊗ B)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.cInternal`:

```lean
@[irreducible] def cInternal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A) ⊗
        (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B) :=
  (eta Λ f A ⊗ₘ eta Λ f B) ≫
    Functor.LaxMonoidal.μ (DerivedCategory.Q (C := internalModules Λ X))
      ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.aSection`:

```lean
@[irreducible] def aSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj
        ((tensor Λ Y).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj (P ⊗ Q)) :=
  (derivedPullback Λ f).map ((qTensor Λ Y).app (P, Q)) ≫
    epsilon Λ f ((totalTensor Λ Y).obj (P, Q))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.cSection`:

```lean
@[irreducible] def cSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (tensor Λ X).obj
        ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P),
          (derivedPullback Λ f).obj (DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q) :=
  (tensor Λ X).map (Prod.mkHom (epsilon Λ f P) (epsilon Λ f Q)) ≫
    (qTensor Λ X).app ((totalSectionPull Λ f).obj P, (totalSectionPull Λ f).obj Q)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.e`:

```lean
@[irreducible] def e (T : Scheme.{u}) :
    (derivedEquivalence Λ T).functor.obj
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (internalModules Λ T) ℤ))) ⟶
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ T) ℤ)) :=
  (sectionLocalizationComparison Λ T (𝟙_ (CochainComplex (internalModules Λ T) ℤ))).hom ≫
    DerivedCategory.Q.map (totalUnitComparison Λ T).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.Equations`:

```lean
@[irreducible] def Equations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) : Prop :=
  ((derivedEquivalence Λ X).functor.map (eta Λ f A) ≫ d Λ f A =
    j Λ f A ≫ epsilon Λ f ((totalSectionEquivalence Λ Y).obj A)) ∧
  ((derivedEquivalence Λ X).functor.map (aInternal Λ f A B) ≫ dZ Λ f A B =
    jTensor Λ f A B ≫ aSection Λ f ((totalSectionEquivalence Λ Y).obj A)
      ((totalSectionEquivalence Λ Y).obj B)) ∧
  ((derivedEquivalence Λ X).functor.map (cInternal Λ f A B) ≫ dOut Λ f A B =
    kTensor Λ f A B ≫ cSection Λ f ((totalSectionEquivalence Λ Y).obj A)
      ((totalSectionEquivalence Λ Y).obj B)) ∧
  ((derivedEquivalence Λ X).functor.map
      (DerivedCategory.Q.map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f A B =
    dZ Λ f A B ≫ DerivedCategory.Q.map
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj A)
        ((totalSectionEquivalence Λ Y).obj B)).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.UnitEquation`:

```lean
@[irreducible] def UnitEquation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (derivedEquivalence Λ X).functor.map
      (eta Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map (actualInternalTotalUnit Λ f)) ≫ e Λ X =
    (derivedPullComparison Λ f).hom.app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))) ≫
      (derivedPullback Λ f).map (e Λ Y) ≫
      epsilon Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
      DerivedCategory.Q.map (sectionTotalUnit Λ f)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.Naturality`:

```lean
@[irreducible] def Naturality {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (A B A' B' : CochainComplex (internalModules Λ Y) ℤ)
      (_hA : KFlatSectionComparison.internalResolving Λ Y A)
      (_hB : KFlatSectionComparison.internalResolving Λ Y B)
      (_hA' : KFlatSectionComparison.internalResolving Λ Y A')
      (_hB' : KFlatSectionComparison.internalResolving Λ Y B') (a : A ⟶ A') (b : B ⟶ B'),
    ((derivedEquivalence Λ X).functor.map
          ((internalDerivedPullback Λ f).map (DerivedCategory.Q.map a)) ≫
        (derivedEquivalence Λ X).functor.map (eta Λ f A') ≫ d Λ f A' =
      (derivedEquivalence Λ X).functor.map (eta Λ f A) ≫ d Λ f A ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a))) ∧
    ((derivedEquivalence Λ X).functor.map ((internalDerivedPullback Λ f).map
          (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b)) ≫
        (derivedEquivalence Λ X).functor.map (aInternal Λ f A' B') ≫ dZ Λ f A' B' =
      (derivedEquivalence Λ X).functor.map (aInternal Λ f A B) ≫ dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map
          ((totalSectionEquivalence Λ Y).map a ⊗ₘ (totalSectionEquivalence Λ Y).map b))) ∧
    ((derivedEquivalence Λ X).functor.map
          ((internalDerivedPullback Λ f).map (DerivedCategory.Q.map a) ⊗ₘ
            (internalDerivedPullback Λ f).map (DerivedCategory.Q.map b)) ≫
        (derivedEquivalence Λ X).functor.map (cInternal Λ f A' B') ≫ dOut Λ f A' B' =
      (derivedEquivalence Λ X).functor.map (cInternal Λ f A B) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b))) ∧
    ((derivedEquivalence Λ X).functor.map
          (DerivedCategory.Q.map ((totalInternalPull Λ f).map (a ⊗ₘ b))) ≫
        (derivedEquivalence Λ X).functor.map
          (DerivedCategory.Q.map (actualInternalTotalIso Λ f A' B').hom) ≫ dOut Λ f A' B' =
      (derivedEquivalence Λ X).functor.map
          (DerivedCategory.Q.map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b)))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.SubstitutionEquations`:

```lean
@[irreducible] def SubstitutionEquations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ)
    (P Q : CochainComplex (modules Λ Y) ℤ)
    (σ : (totalSectionEquivalence Λ Y).obj A ≅ P)
    (τ : (totalSectionEquivalence Λ Y).obj B ≅ Q) : Prop :=
  ((derivedEquivalence Λ X).functor.map (eta Λ f A) ≫ d Λ f A ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom) =
      j Λ f A ≫ (derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom) ≫
        epsilon Λ f P) ∧
  ((derivedEquivalence Λ X).functor.map (aInternal Λ f A B) ≫ dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (σ.hom ⊗ₘ τ.hom)) =
      jTensor Λ f A B ≫ (derivedPullback Λ f).map
          ((tensor Λ Y).map (Prod.mkHom (DerivedCategory.Q.map σ.hom)
            (DerivedCategory.Q.map τ.hom))) ≫ aSection Λ f P Q) ∧
  ((derivedEquivalence Λ X).functor.map (cInternal Λ f A B) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom ⊗ₘ
          (totalSectionPull Λ f).map τ.hom) =
      kTensor Λ f A B ≫ (tensor Λ X).map (Prod.mkHom
          ((derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom))
          ((derivedPullback Λ f).map (DerivedCategory.Q.map τ.hom))) ≫ cSection Λ f P Q) ∧
  ((derivedEquivalence Λ X).functor.map
        (DerivedCategory.Q.map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom ⊗ₘ
          (totalSectionPull Λ f).map τ.hom) =
      dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (σ.hom ⊗ₘ τ.hom)) ≫
        DerivedCategory.Q.map (sectionTotalIso Λ f P Q).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.UnitSubstitution`:

```lean
@[irreducible] def UnitSubstitution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (modules Λ Y) ℤ)
    (σ : 𝟙_ (CochainComplex (modules Λ Y) ℤ) ≅ P) : Prop :=
  (derivedEquivalence Λ X).functor.map
      (eta Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map (actualInternalTotalUnit Λ f)) ≫ e Λ X =
    (derivedPullComparison Λ f).hom.app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))) ≫
      (derivedPullback Λ f).map (e Λ Y ≫ DerivedCategory.Q.map σ.hom) ≫
      epsilon Λ f P ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map σ.inv ≫ sectionTotalUnit Λ f)
```

## New

`Sheaf.Paper.SectionModuleOperationsData.equivalence`:

```lean
@[reducible] def equivalence (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)
```

`Sheaf.Paper.SectionDerivedTensorData.internalTotalTensor`:

```lean
def internalTotalTensor [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
    (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ × CochainComplex (internalModules Λ X) ℤ ⥤
      CochainComplex (internalModules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (internalModules Λ X))
```

`Sheaf.Paper.SectionDerivedTensorData.totalTensor`:

```lean
def totalTensor [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
    (X : Scheme.{u}) :
    CochainComplex (modules Λ X) ℤ × CochainComplex (modules Λ X) ℤ ⥤
      CochainComplex (modules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (modules Λ X))
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionOrdinaryMonoidal`:

```lean
instance totalSectionOrdinaryMonoidal (X : Scheme.{u}) :
    MonoidalCategory (modules Λ X) := inferInstance

-- Use the canonical ordinary structure when constructing the cochain caches below.
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalGraded`:

```lean
instance totalInternalGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionGraded`:

```lean
instance totalSectionGraded (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalGoodLeft`:

```lean
instance totalInternalGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalGoodRight`:

```lean
instance totalInternalGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalTensorFour`:

```lean
instance totalInternalTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionGoodLeft`:

```lean
instance totalSectionGoodLeft (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q H := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionGoodRight`:

```lean
instance totalSectionGoodRight (X : Scheme.{u})
    (P Q H : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q H := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionTensorFour`:

```lean
instance totalSectionTensorFour (X : Scheme.{u})
    (P Q H K : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q H K := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalHasTensor`:

```lean
instance (priority := 4000) totalInternalHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionHasTensor`:

```lean
instance (priority := 4000) totalSectionHasTensor (X : Scheme.{u})
    (P Q : CochainComplex (modules Λ X) ℤ) :
    HomologicalComplex.HasTensor P Q := inferInstance
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalMonoidal`:

```lean
@[reducible] def totalInternalMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (internalModules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionMonoidal`:

```lean
@[reducible] def totalSectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategory (modules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionCochainTensorComparison.totalInternalMonoidalStruct`:

```lean
@[reducible] def totalInternalMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (internalModules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (internalModules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionCochainTensorComparison.totalSectionMonoidalStruct`:

```lean
@[reducible] def totalSectionMonoidalStruct
    (X : Scheme.{u}) : MonoidalCategoryStruct (CochainComplex (modules Λ X) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (modules Λ X) (.up ℤ)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalInternalPull`:

```lean
@[reducible] def totalInternalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (internalModules Λ Y) ℤ ⥤ CochainComplex (internalModules Λ X) ℤ :=
  retainedCochainFunctor (CondensedRing.upperStar Λ f)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionPull`:

```lean
@[reducible] def totalSectionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CochainComplex (modules Λ Y) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  retainedCochainFunctor (pullback Λ f)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionEquivalence`:

```lean
@[reducible] def totalSectionEquivalence (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  cochainSectionEquivalence Λ X
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalTensorComparison`:

```lean
@[irreducible] def totalTensorComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (totalSectionEquivalence Λ X).obj (P ⊗ Q) ≅
      (totalSectionEquivalence Λ X).obj P ⊗ (totalSectionEquivalence Λ X).obj Q :=
  cochainTensorComparison Λ X P Q
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.totalUnitComparison`:

```lean
@[irreducible] def totalUnitComparison (X : Scheme.{u}) :
    (totalSectionEquivalence Λ X).obj (internalCochainUnit Λ X) ≅
      sectionCochainUnit Λ X :=
  (HomologicalComplex.singleMapHomologicalComplex (equivalence Λ X).functor (.up ℤ) 0).app
      (𝟙_ (internalModules Λ X)) ≪≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).mapIso (ordinaryUnitComparison Λ X)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.actualInternalTotalUnit`:

```lean
@[irreducible] def actualInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalInternalPull Λ f).obj (internalCochainUnit Λ Y) ⟶
      internalCochainUnit Λ X :=
  (HomologicalComplex.singleMapHomologicalComplex (CondensedRing.upperStar Λ f)
    (.up ℤ) 0).hom.app (𝟙_ (internalModules Λ Y)) ≫
    (HomologicalComplex.single (internalModules Λ X) (.up ℤ) 0).map
      (normalizationInternalUnit Λ f)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.sectionTotalUnit`:

```lean
@[irreducible] def sectionTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (sectionCochainUnit Λ Y) ⟶
      sectionCochainUnit Λ X :=
  (HomologicalComplex.singleMapHomologicalComplex (pullback Λ f) (.up ℤ) 0).hom.app
      (𝟙_ (modules Λ Y)) ≫
    (HomologicalComplex.single (modules Λ X) (.up ℤ) 0).map (normalizationSectionUnit Λ f)
```

`Sheaf.Paper.SectionTotalOplaxComparisonData.conjugatedInternalTotalUnit`:

```lean
def conjugatedInternalTotalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (sectionCochainUnit Λ Y) ⟶
      sectionCochainUnit Λ X :=
  (totalSectionPull Λ f).map (totalUnitComparison Λ Y).inv ≫
    (termwisePullComparison Λ f (internalCochainUnit Λ Y)).inv ≫
    (totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
    (totalUnitComparison Λ X).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.eta`:

```lean
@[irreducible] def eta {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A) ⟶
      (internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj A) :=
  by
    with_unfolding_all
      exact (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj A)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.epsilon`:

```lean
@[irreducible] def epsilon {X Y : Scheme.{u}} (f : X ⟶ Y) (P : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P) :=
  by
    with_unfolding_all exact (pullback Λ f).mapDerivedCategoryFactors.hom.app P
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.d`:

```lean
@[irreducible] def d {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj A)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj A)) :=
  (cochainLocalizationIso Λ X ((totalInternalPull Λ f).obj A)).hom ≫
    DerivedCategory.Q.map (termwisePullComparison Λ f A).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.j`:

```lean
@[irreducible] def j {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A)) ⟶
      (derivedPullback Λ f).obj
        (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A)) :=
  (derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A) ≫
    (derivedPullback Λ f).map (cochainLocalizationIso Λ Y A).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.dZ`:

```lean
@[irreducible] def dZ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj (A ⊗ B))) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj
        ((totalSectionEquivalence Λ Y).obj A ⊗ (totalSectionEquivalence Λ Y).obj B)) :=
  d Λ f (A ⊗ B) ≫
    DerivedCategory.Q.map ((totalSectionPull Λ f).map (cochainTensorComparison Λ Y A B).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.dOut`:

```lean
@[irreducible] def dOut {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj ((internalLocalizationFunctor Λ X).obj
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)) ⟶
      DerivedCategory.Q.obj
        ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj A) ⊗
          (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj B)) :=
  (cochainLocalizationIso Λ X
      ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B)).hom ≫
    DerivedCategory.Q.map (cochainTensorComparison Λ X
      ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)).hom ≫
    DerivedCategory.Q.map
      ((termwisePullComparison Λ f A).hom ⊗ₘ (termwisePullComparison Λ f B).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.jTensor`:

```lean
@[irreducible] def jTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj ((internalDerivedPullFunctor Λ f).obj
        ((internalLocalizationFunctor Λ Y).obj A ⊗ (internalLocalizationFunctor Λ Y).obj B)) ⟶
      (derivedPullback Λ f).obj ((tensor Λ Y).obj
        (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A),
          DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj B))) :=
  (derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A ⊗
      (internalLocalizationFunctor Λ Y).obj B) ≫
    (derivedPullback Λ f).map
      ((derivedSectionTensorIso Λ Y ((internalLocalizationFunctor Λ Y).obj A)
          ((internalLocalizationFunctor Λ Y).obj B)).hom ≫
        (tensor Λ Y).map (Prod.mkHom (cochainLocalizationIso Λ Y A).hom
          (cochainLocalizationIso Λ Y B).hom))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.kTensor`:

```lean
@[irreducible] def kTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (derivedSectionFunctor Λ X).obj
        ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A) ⊗
          (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj B)) ⟶
      (tensor Λ X).obj
        ((derivedPullback Λ f).obj
            (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj A)),
          (derivedPullback Λ f).obj
            (DerivedCategory.Q.obj ((totalSectionEquivalence Λ Y).obj B))) :=
  (derivedSectionTensorIso Λ X
    ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A))
    ((internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj B))).hom ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj A))
      ((derivedPullSquare Λ f).hom.app ((internalLocalizationFunctor Λ Y).obj B))) ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullback Λ f).map (cochainLocalizationIso Λ Y A).hom)
      ((derivedPullback Λ f).map (cochainLocalizationIso Λ Y B).hom))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.aInternal`:

```lean
@[irreducible] def aInternal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A ⊗
        (internalLocalizationFunctor Λ Y).obj B) ⟶
      (internalLocalizationFunctor Λ X).obj ((totalInternalPull Λ f).obj (A ⊗ B)) :=
  (internalDerivedPullFunctor Λ f).map
      (internalQTensorArrow Λ Y A B) ≫
    eta Λ f (A ⊗ B)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.cInternal`:

```lean
@[irreducible] def cInternal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj A) ⊗
        (internalDerivedPullFunctor Λ f).obj ((internalLocalizationFunctor Λ Y).obj B) ⟶
      (internalLocalizationFunctor Λ X).obj
        ((totalInternalPull Λ f).obj A ⊗ (totalInternalPull Λ f).obj B) :=
  (eta Λ f A ⊗ₘ eta Λ f B) ≫
    internalQTensorArrow Λ X
      ((totalInternalPull Λ f).obj A) ((totalInternalPull Λ f).obj B)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.aSection`:

```lean
@[irreducible] def aSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj
        ((tensor Λ Y).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj (P ⊗ Q)) :=
  (derivedPullback Λ f).map (qTensorArrow Λ Y P Q) ≫
    epsilon Λ f (P ⊗ Q)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.cSection`:

```lean
@[irreducible] def cSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (tensor Λ X).obj
        ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P),
          (derivedPullback Λ f).obj (DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q) :=
  (tensor Λ X).map (Prod.mkHom (epsilon Λ f P) (epsilon Λ f Q)) ≫
    qTensorArrow Λ X ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.e`:

```lean
@[irreducible] def e (T : Scheme.{u}) :
    (derivedSectionFunctor Λ T).obj
        ((internalLocalizationFunctor Λ T).obj (internalCochainUnit Λ T)) ⟶
      DerivedCategory.Q.obj (sectionCochainUnit Λ T) :=
  (cochainLocalizationIso Λ T (internalCochainUnit Λ T)).hom ≫
    DerivedCategory.Q.map (cochainUnitComparison Λ T).hom
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.Equations`:

```lean
@[irreducible] def Equations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) : Prop :=
  ((derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A =
    j Λ f A ≫ epsilon Λ f ((totalSectionEquivalence Λ Y).obj A)) ∧
  ((derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B =
    jTensor Λ f A B ≫ aSection Λ f ((totalSectionEquivalence Λ Y).obj A)
      ((totalSectionEquivalence Λ Y).obj B)) ∧
  ((derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B =
    kTensor Λ f A B ≫ cSection Λ f ((totalSectionEquivalence Λ Y).obj A)
      ((totalSectionEquivalence Λ Y).obj B)) ∧
  ((derivedSectionFunctor Λ X).map
      ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f A B =
    dZ Λ f A B ≫ DerivedCategory.Q.map
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj A)
        ((totalSectionEquivalence Λ Y).obj B)).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.UnitEquation`:

```lean
@[irreducible] def UnitEquation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (derivedSectionFunctor Λ X).map
      (eta Λ f (internalCochainUnit Λ Y) ≫
        (internalLocalizationFunctor Λ X).map (internalPullUnitArrow Λ f)) ≫ e Λ X =
    (derivedPullSquare Λ f).hom.app
        ((internalLocalizationFunctor Λ Y).obj (internalCochainUnit Λ Y)) ≫
      (derivedPullback Λ f).map (e Λ Y) ≫
      epsilon Λ f (sectionCochainUnit Λ Y) ≫
      DerivedCategory.Q.map (sectionPullUnitArrow Λ f)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.Naturality`:

```lean
@[irreducible] def Naturality {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (A B A' B' : CochainComplex (internalModules Λ Y) ℤ)
      (_hA : KFlatSectionComparison.internalResolving Λ Y A)
      (_hB : KFlatSectionComparison.internalResolving Λ Y B)
      (_hA' : KFlatSectionComparison.internalResolving Λ Y A')
      (_hB' : KFlatSectionComparison.internalResolving Λ Y B') (a : A ⟶ A') (b : B ⟶ B'),
    ((derivedSectionFunctor Λ X).map
          ((internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a)) ≫
        (derivedSectionFunctor Λ X).map (eta Λ f A') ≫ d Λ f A' =
      (derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a))) ∧
    ((derivedSectionFunctor Λ X).map ((internalDerivedPullFunctor Λ f).map
          ((internalLocalizationFunctor Λ Y).map a ⊗ₘ (internalLocalizationFunctor Λ Y).map b)) ≫
        (derivedSectionFunctor Λ X).map (aInternal Λ f A' B') ≫ dZ Λ f A' B' =
      (derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map
          ((totalSectionEquivalence Λ Y).map a ⊗ₘ (totalSectionEquivalence Λ Y).map b))) ∧
    ((derivedSectionFunctor Λ X).map
          ((internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map a) ⊗ₘ
            (internalDerivedPullFunctor Λ f).map ((internalLocalizationFunctor Λ Y).map b)) ≫
        (derivedSectionFunctor Λ X).map (cInternal Λ f A' B') ≫ dOut Λ f A' B' =
      (derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b))) ∧
    ((derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map ((totalInternalPull Λ f).map (a ⊗ₘ b))) ≫
        (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A' B').hom) ≫ dOut
              Λ f A' B' =
      (derivedSectionFunctor Λ X).map
          ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ
              f A B ≫
        DerivedCategory.Q.map
          ((totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map a) ⊗ₘ
            (totalSectionPull Λ f).map ((totalSectionEquivalence Λ Y).map b)))
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.SubstitutionEquations`:

```lean
@[irreducible] def SubstitutionEquations {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ)
    (P Q : CochainComplex (modules Λ Y) ℤ)
    (σ : (totalSectionEquivalence Λ Y).obj A ≅ P)
    (τ : (totalSectionEquivalence Λ Y).obj B ≅ Q) : Prop :=
  ((derivedSectionFunctor Λ X).map (eta Λ f A) ≫ d Λ f A ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom) =
      j Λ f A ≫ (derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom) ≫
        epsilon Λ f P) ∧
  ((derivedSectionFunctor Λ X).map (aInternal Λ f A B) ≫ dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (σ.hom ⊗ₘ τ.hom)) =
      jTensor Λ f A B ≫ (derivedPullback Λ f).map
          ((tensor Λ Y).map (Prod.mkHom (DerivedCategory.Q.map σ.hom)
            (DerivedCategory.Q.map τ.hom))) ≫ aSection Λ f P Q) ∧
  ((derivedSectionFunctor Λ X).map (cInternal Λ f A B) ≫ dOut Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom ⊗ₘ
          (totalSectionPull Λ f).map τ.hom) =
      kTensor Λ f A B ≫ (tensor Λ X).map (Prod.mkHom
          ((derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom))
          ((derivedPullback Λ f).map (DerivedCategory.Q.map τ.hom))) ≫ cSection Λ f P Q) ∧
  ((derivedSectionFunctor Λ X).map
        ((internalLocalizationFunctor Λ X).map (actualInternalTotalIso Λ f A B).hom) ≫ dOut Λ f
            A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map σ.hom ⊗ₘ
          (totalSectionPull Λ f).map τ.hom) =
      dZ Λ f A B ≫
        DerivedCategory.Q.map ((totalSectionPull Λ f).map (σ.hom ⊗ₘ τ.hom)) ≫
        DerivedCategory.Q.map (sectionTotalIso Λ f P Q).hom)
```

`Sheaf.Paper.SectionResolutionConjugationIdentities.UnitSubstitution`:

```lean
@[irreducible] def UnitSubstitution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (modules Λ Y) ℤ)
    (σ : sectionCochainUnit Λ Y ≅ P) : Prop :=
  (derivedSectionFunctor Λ X).map
      (eta Λ f (internalCochainUnit Λ Y) ≫
        (internalLocalizationFunctor Λ X).map (internalPullUnitArrow Λ f)) ≫ e Λ X =
    (derivedPullSquare Λ f).hom.app
        ((internalLocalizationFunctor Λ Y).obj (internalCochainUnit Λ Y)) ≫
      (derivedPullback Λ f).map (e Λ Y ≫ DerivedCategory.Q.map σ.hom) ≫
      epsilon Λ f P ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map σ.inv ≫ sectionPullUnitArrow Λ f)
```

New constructed API `Sheaf.Paper.SectionCochainTensorComparison.retainedCochainObject`:

```lean
@[reducible] def retainedCochainObject
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (P : CochainComplex C ℤ) :
    CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj P
```

New constructed API `Sheaf.Paper.SectionCochainTensorComparison.retainedCochainMap`:

```lean
@[reducible] def retainedCochainMap
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {P Q : CochainComplex C ℤ} (a : P ⟶ Q) :
    retainedCochainObject F P ⟶ retainedCochainObject F Q :=
  (F.mapHomologicalComplex (.up ℤ)).map a
```

New constructed API `Sheaf.Paper.SectionCochainTensorComparison.retainedCochainFunctor`:

```lean
@[reducible] def retainedCochainFunctor
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] : CochainComplex C ℤ ⥤ CochainComplex D ℤ where
  obj := retainedCochainObject F
  map := retainedCochainMap F
  map_id P := (F.mapHomologicalComplex (.up ℤ)).map_id P
  map_comp a b := (F.mapHomologicalComplex (.up ℤ)).map_comp a b
```

New constructed API `Sheaf.Paper.SectionCochainTensorComparison.retainedCochainFunctor_eq`:

```lean
theorem retainedCochainFunctor_eq
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    retainedCochainFunctor F = F.mapHomologicalComplex (.up ℤ) := rfl
```

New constructed API `Sheaf.Paper.SectionCochainTensorComparison.cochainSectionEquivalence`:

```lean
@[implicit_reducible] def cochainSectionEquivalence (X : Scheme.{u}) :
    CochainComplex (internalModules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ :=
  retainedCochainFunctor (equivalence Λ X).functor
```

New constructed API `Sheaf.Paper.SectionTotalOplaxComparisonData.totalSectionPullMonoidal`:

```lean
instance totalSectionPullMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).Monoidal := by
  change ((pullback Λ f).mapHomologicalComplex (.up ℤ)).Monoidal
  infer_instance
```

The other new component APIs and their full signatures are recorded in the two new modules and their definition nodes. All are constructed from the original data; all their API theorems are proved. No private helper appears in a public definition or signature.

The original `SectionOplaxTotalComparison.equivalence_total_summand` fails at
line 359: `unfold totalComparison` cannot unfold through the new irreducible
`cochainTensorComparison` interface. This unclaimed module has exactly one changed
proof line, with all declaration signatures and visibility retained:

```lean
-- Old:
  unfold totalTensorComparison totalComparison
-- New:
  unfold totalTensorComparison cochainTensorComparison totalComparison
```

## Users

The source-only downstream scan was rerun for every changed declaration family.
An additional import-graph scan includes the archived sources under quarantine,
retaining their consumers even when the current library import graph omits them.
The archive scan requires the relevant namespace to be open or qualified; the standard tool also over-approximates unqualified name matches. Every statement keeps
its meaning: all fixed data are definitionally identical. SectionOplaxTotalComparison has only the forced one-line unfolding adaptation
below; all other consumer sources remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedFlatTensorContinuity | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.CoefficientScalarSectionRealization | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.CoefficientScalarTensorData | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.CoefficientScalarTensorRepresentative | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.CountableNormProjectionCriterion | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.FilteredFlatTensorCohomology | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarDerivedComparison | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteScalarModelDefinitions | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.InternalDirectImageLaxRealization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.InternalOplaxResolvingComponents | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.InternalScalarMateProjection | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.InternalScalarProjectionMate | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.InternalScalarPullbackNormalizationData | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.ModuleSectionDerivedComparisonSquare | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.QuotientSectionTensorNormalization | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | unclaimed | Archived consumer retained; identical fixed data; source and attachment unchanged. |
| Sheaf.Paper.ScalarChangeDirectImageUnit | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionCochainTensorComparison | new, G6 | Constructed interface and proved API for the original data. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionDerivedRepresentativeSquare | U3 | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Representation and shared-interface changes detailed above; same mathematical data. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Representation and shared-interface changes detailed above; same mathematical data. |
| Sheaf.Paper.SectionOpenGeneratorScalar | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionOplaxTotalComparison | unclaimed | Forced one-line proof unfolding of cochainTensorComparison; original signature and all other lines retained. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionOrdinaryPullCompatibility | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionPullComputationOfRealization | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionPullNormalizationTransport | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionRepresentativeTensorArrow | new, G6 | Constructed interface and proved API for the original data. |
| Sheaf.Paper.SectionResolutionConjugationIdentities | G6 | Complete proof; original theorem signature verbatim. |
| Sheaf.Paper.SectionResolvingOplaxConstraintData | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionScalarComputationAll | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionScalarComputationTransport | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionTensorConjugateComputation | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionTensorNormalizationTransport | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionTensorRightComputation | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | Representation and shared-interface changes detailed above; same mathematical data. |
| Sheaf.SixFunctors.ScalarSixDefinitions | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixGeometry | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixImmersionComparison | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixOpenComparison | unclaimed | Identical fixed data; statement and source unchanged; no adaptation. |

## Status

landed 20261026T182250-L-3543761 2026-10-26 (merge of deliver/G6/Sheaf.Paper.SectionResolutionConjugationIdentities)
