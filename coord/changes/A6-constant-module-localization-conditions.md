# ConstantModuleDerivedProjection localization equations

## Reason

Specializing the generic exact-derived mate proof to module sheaves made the kernel
repeatedly compare complex constructions using the sheaf zero morphisms with the same
constructions using abelian-induced zero morphisms. The original concrete normalization
formulas repeat this conversion throughout each equation. A diagnostic specialization
of the right normalization reached a kernel heartbeat timeout; its reduction trace
expanded tens of thousands of additions and scalar actions.

The repair names the generic left and right localization equations and makes the
existing concrete predicates their specializations. No hypothesis or equation is dropped.
The new definitions have no holes. Existing public signatures stay unchanged.


## Old

```lean
def LeftLocalizationSquare (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (left : d.pullR.mapDerivedCategory ⋙ onDerived K A ≅
      onDerived J A ⋙ d.pullA.mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (Modules J A) ℤ,
        left.hom.app (DerivedCategory.Q.obj P) ≫
          d.pullA.mapDerivedCategory.map ((restriction J A).mapDerivedCategoryFactors.hom.app P) ≫
          d.pullA.mapDerivedCategoryFactors.hom.app ((onComplexes J A).obj P) =
        (onDerived K A).map (d.pullR.mapDerivedCategoryFactors.hom.app P) ≫
          (restriction K A).mapDerivedCategoryFactors.hom.app
            ((d.pullR.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o.left (.up ℤ)).hom.app P)

/-- Localization normalization of the right-derived comparison.
Source: Stacks Tag 07A6
(blueprint: def-sfb-constant-module-derived-comparison-data). -/
def RightLocalizationSquare (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (right : d.pushR.rightDerivedFunctor ⋙ onDerived J A ≅
      onDerived K A ⋙ d.pushA.rightDerivedFunctor) : Prop :=
  ∀ P : CochainComplex (Modules K A) ℤ,
        (onDerived J A).map
            (d.pushR.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          right.hom.app (DerivedCategory.Q.obj P) ≫
          d.pushA.rightDerivedFunctor.map ((restriction K A).mapDerivedCategoryFactors.hom.app P) =
        (restriction J A).mapDerivedCategoryFactors.hom.app
            ((d.pushR.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o.right (.up ℤ)).hom.app P) ≫
          d.pushA.rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj ((onComplexes K A).obj P))

```

## New

```lean
def LeftLocalizationCondition
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [Abelian B] [Abelian E] [Abelian F] [Abelian H]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasDerivedCategory F] [HasDerivedCategory H]
    (L : B ⥤ E) (L' : F ⥤ H) (S : B ⥤ F) (T : E ⥤ H)
    [L.Additive] [L'.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (oL : L ⋙ T ≅ S ⋙ L')
    (left : L.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ L'.mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex B ℤ,
    left.hom.app (DerivedCategory.Q.obj P) ≫
      L'.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app P) ≫
      L'.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) =
    T.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      T.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oL (.up ℤ)).hom.app P)

/-- The right localization equation, with the four ordinary functors kept as parameters.
Source: Stacks Tag 07A6
(blueprint: def-sfb-constant-module-derived-comparison-data).
This shared equation keeps scalar-restriction functors abstract during specialization. -/
def RightLocalizationCondition
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [Abelian B] [Abelian E] [Abelian F] [Abelian H]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasDerivedCategory F] [HasDerivedCategory H]
    [HasKInjectiveResolutions E] [HasKInjectiveResolutions H]
    (R : E ⥤ B) (R' : H ⥤ F) (S : B ⥤ F) (T : E ⥤ H)
    [R.Additive] [R'.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (oR : R ⋙ S ≅ T ⋙ R')
    (right : R.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      T.mapDerivedCategory ⋙ R'.rightDerivedFunctor) : Prop :=
  ∀ P : CochainComplex E ℤ,
    S.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      right.hom.app (DerivedCategory.Q.obj P) ≫
      R'.rightDerivedFunctor.map (T.mapDerivedCategoryFactors.hom.app P) =
    S.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oR (.up ℤ)).hom.app P) ≫
      R'.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((T.mapHomologicalComplex (.up ℤ)).obj P))

def LeftLocalizationSquare (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (left : d.pullR.mapDerivedCategory ⋙ onDerived K A ≅
      onDerived J A ⋙ d.pullA.mapDerivedCategory) : Prop :=
  LeftLocalizationCondition d.pullR d.pullA (restriction J A) (restriction K A)
    o.left left

/-- Localization normalization of the right-derived comparison.
Source: Stacks Tag 07A6
(blueprint: def-sfb-constant-module-derived-comparison-data). -/
def RightLocalizationSquare (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (right : d.pushR.rightDerivedFunctor ⋙ onDerived J A ≅
      onDerived K A ⋙ d.pushA.rightDerivedFunctor) : Prop :=
  RightLocalizationCondition d.pushR d.pushA (restriction J A) (restriction K A)
    o.right right

```

`LeftLocalizationCondition` and `RightLocalizationCondition` contain the exact generic
versions of the displayed equations. Their full definitions are in the adapted module.
Local instance selection uses the additive and zero structures induced by the recorded
abelian categories when elaborating those equations.

The bounded-below consumer keeps every field unchanged and adds the same local
instance-selection commands before its universe declaration:

```lean
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms
```

The four attributes are the complete change to that consumer; its old source had no
such local selection. These cached instances are definitionally the abelian-induced
ones, so this changes elaboration terms without changing the field equations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData` | unclaimed | Defines the factored predicates and unchanged comparison package. |
| `Sheaf.CategoryTheory.ConstantModulePlusComparisonData` | unclaimed | Consumer of DerivedIdentification; selects the same abelian-induced additive structures locally; signature and field equations unchanged. |
| `Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification` | A6 | Generic normalization helpers use the named equations; concrete assembly specializes them. |
| `Sheaf.CategoryTheory.ConstantModuleOrdinaryRealization` | new A6 node | Imports the data interface; its ordinary conclusion is unaffected. |
| `Sheaf.CategoryTheory.ConstantModuleTensorSquareDescent` | new A6 node | Uses the unchanged LeftLocalizationSquare signature. |

The source scan was `tools/downstream.py
Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData --uses RightLocalizationSquare
DerivedIdentification`. It lists the two existing downstream modules above. No Challenge
target signature changes; the equations represented by its transitive definition
interface are preserved. The independent definition review applies to this repair.

## Status

landed 20261023T230345-L-3418115 2026-10-23 (merge of deliver/A6/Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification)
