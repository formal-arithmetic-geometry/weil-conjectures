# WeilConjectures.PointTransportCone canonical interfaces

## Reason

Remove a redundant equality cast between the two definitionally identical reduction
presentations. Profiling the original presentation showed 12 seconds in the conversion
of reductionUnit to its underlying map, plus repeated costly conversions in consumers.
The explicit result type retains the original domain and codomain. The chosen tensor
unit and section functor are unchanged. reductionSectionModel_eq is still proved by rfl;
its equality transport is the identity, so the old composite equals the new map by
Category.comp_id. There is no change to any target meaning or additional hypothesis.

The associated API definitions now have explicit result types, definitionally equal to their
original inferred types: sectionsFactors, reductionEnd, augmentation, coneSections, coneArrow,
resolvedArrow and pullbackRoofIso. Their bodies are unchanged. This keeps the canonical functor and Roos
presentations in consumer types instead of repeatedly unfolding the underlying mapping cocone,
section-complex construction and localization implementation. The compiler checks each old
construction against its explicit interface. No target statement or universe is changed.

The two tower functors now expose their objects through the named constructions
reductionTower and pullbackTower. Their maps and functor laws are the original ones.
This prevents comparisons of iota.obj P with P.obj from expanding the entire tower's
sectionwise module actions. The private theorems reductionTowers_eq_original and
pullbackTowers_eq_original prove equality of the whole functors by unfolding these
wrappers and reflexivity. This is a representation change with identical objects,
transitions and actions on every chain map. The new helpers realize the existing
node's D(P) and B(P) constructions; no new mathematical statement is introduced.

The aliases sections and moduleQ are now named definitions rather than abbreviations,
with their original bodies and inferred types. Their local implicit transparency permits
all existing concrete map equations. This changes no object, morphism or instance, and
keeps the functor names in proof terms instead of eagerly expanding their implementations.

## Old

```lean
abbrev sections := (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)
abbrev moduleQ := CompletedStalk.moduleQ l E
```

```lean
def sectionsFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) _ _ _
```

```lean
def reductionTowers :=
  (Functor.ofOpSequence (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)
```

```lean
def pullbackTowers :=
  integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)
```

```lean
def reductionUnit
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :=
  (sections D l E).map (unrestrictedTowerUnit l E (Spec (.of D.k)) P n) ≫
    eqToHom (reductionSectionModel_eq D l E P n)
```

```lean
def reductionEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ ((reductionTowers D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((reductionTowers D l E).obj P))
```

```lean
def augmentation (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  CochainComplex.mappingCocone.lift
    (reductionEnd D l E P)
    (reductionProduct D l E P) 0
    (augmentation_condition D l E P)
```

```lean
def coneSections (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  CompletedStalk.sectionsRoos D l E
    ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P)
```

```lean
def coneArrow (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :=
  (moduleQ l E).map (augmentation D l E P ≫ integralOperationsRoosMap v)
```

```lean
def resolvedArrow
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :=
  (sectionsFactors D l E).hom.app P ≫ coneArrow D l E P v
```

```lean
def pullbackRoofIso
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :=
  @asIso _ _ _ _
    ((moduleQ l E).map (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom)))
    (pullbackRoof_isIso D l E P Q a)
```

## New

```lean
def sections := (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)
def moduleQ := CompletedStalk.moduleQ l E
```

```lean
def reductionTower
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  ((Functor.ofOpSequence (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip.obj P) ⋙ sections D l E
```

```lean
def pullbackTower
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  (integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P ⋙
    sections D l E
```

```lean
def sectionsFactors :
    @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) ⋙
        pointFibreIntegralAmbient D l E ≅ sections D l E ⋙ moduleQ l E :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) _ _ _
```

```lean
def reductionTowers :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  let F := (Functor.ofOpSequence
    (X := unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)))
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)
  { obj := reductionTower D l E
    map := F.map
    map_id := F.map_id
    map_comp := F.map_comp }
```

```lean
def pullbackTowers :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  let F := integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections D l E)
  { obj := pullbackTower D l E
    map := F.map
    map_id := F.map_id
    map_comp := F.map_comp }
```

```lean
def reductionUnit
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    (sections D l E).obj P ⟶ ((reductionTowers D l E).obj P).obj (op n) :=
  (sections D l E).map (unrestrictedTowerUnit l E (Spec (.of D.k)) P n)
```

```lean
def reductionEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    End (∏ᶜ fun n ↦ ((reductionTowers D l E).obj P).obj (op n)) :=
  towerTransitionEndomorphism (K := fun n ↦ ((reductionTowers D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((reductionTowers D l E).obj P))
```

```lean
def augmentation (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sections D l E).obj P ⟶ integralOperationsRoos ((reductionTowers D l E).obj P) :=
  CochainComplex.mappingCocone.lift
    (reductionEnd D l E P)
    (reductionProduct D l E P) 0
    (augmentation_condition D l E P)
```

```lean
def coneSections (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sections D l E).obj
        ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj P) ≅
      integralOperationsRoos ((pullbackTowers D l E).obj P) :=
  CompletedStalk.sectionsRoos D l E
    ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P)
```

```lean
def coneArrow (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :
    (moduleQ l E).obj ((sections D l E).obj P) ⟶
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P)) :=
  (moduleQ l E).map (augmentation D l E P ≫ integralOperationsRoosMap v)
```

```lean
def resolvedArrow
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionTowers D l E).obj P ⟶ (pullbackTowers D l E).obj P) :
    (pointFibreIntegralAmbient D l E).obj (DerivedCategory.Q.obj P) ⟶
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P)) :=
  (sectionsFactors D l E).hom.app P ≫ coneArrow D l E P v
```

```lean
def pullbackRoofIso
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (a : Q ⟶ P) [QuasiIso a.hom] :
    (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj Q.obj)) ≅
      (moduleQ l E).obj (integralOperationsRoos ((pullbackTowers D l E).obj P.obj)) :=
  @asIso _ _ _ _
    ((moduleQ l E).map (integralOperationsRoosMap ((pullbackTowers D l E).map a.hom)))
    (pullbackRoof_isIso D l E P Q a)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.PointTransportConeComparisonDescent --uses reductionUnit`
reports only the item itself and zero downstream modules. The module's public theorem
statements are unchanged; their proofs use the same section map of the same tensor unit.
No module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointTransportConeComparisonDescent | R2 | Same maps and isomorphisms, explicit original result types; redundant unit cast removed. |

## Status

landed 20261026T070744-L-3653604 2026-10-26 (merge of deliver/R2/Sheaf.Paper.PointTransportConeComparisonDescent)
