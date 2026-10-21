/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.IntegralTensorComparisonSystem

/-! # Tensor comparisons through rationalization and common finite fields

Source: Weil blueprint, main-20261015, order 1826, final coefficient paragraph,
and order 1868; the conditional descent argument of the DAG
(blueprint: def-sf-rational-tensor-comparison-system).

All raw localizations and common-stage quotients below are the existing constructions.
The auxiliary records only organize the hypotheses and the normalized conclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u c h

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace WeilConjectures.TensorComparisonDescent

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

variable {l Ω}
  (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear
      (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]

/-- The existing raw localization, with unchanged objects and no idempotent completion.
Source: blueprint order 1826 (blueprint: def-sf-rational-tensor-comparison-system). -/
abbrev Rat (E : Index l Ω) :=
  ScalarLocalization (Integers l Ω E) (C E) (uniformizer l Ω E)

/-- The monoidal structures to be constructed on those fixed rational categories.
Source: blueprint order 1826 (blueprint: def-sf-rational-tensor-comparison-system). -/
class RationalStructures where
  monoidal : ∀ E, MonoidalCategory (Rat C E)
  symmetric : ∀ E, @SymmetricCategory (Rat C E) _ (monoidal E)

attribute [instance_reducible, instance] RationalStructures.monoidal
attribute [instance_reducible, instance] RationalStructures.symmetric

/-- The rational conclusion, including all prescribed component formulas and the
identity and tower equations. HEq only accommodates the explicitly prescribed object
equalities and equal coefficient maps; it never compares unrelated objects.
Source: blueprint orders 1826, 1868 and DAG proof steps 1--5
(blueprint: def-sf-rational-tensor-comparison-system). -/
structure RationalData (A : IntegralData C) [RationalStructures C] where
  F : ∀ E, Rat C E ⥤ D (FieldOf l Ω E)
  object : ∀ E (X : Rat C E),
    (F E).obj X = (fractionB l Ω E).obj
      ((A.F E).obj X.obj)
  perfect : ∀ E (X : Rat C E), DerivedCategory.IsPerfectRingComplex.{u, u} ((F E).obj X)
  finite : ∀ E (X : Rat C E), DerivedCategory.pointFiniteDimensional (FieldOf l Ω E) ((F E).obj X)
  tensor : ∀ E, (F E).CoreMonoidal
  S : StageSystem (Rat C)
  transitionObject : ∀ {E L} (a : E ≤ L) (X : Rat C E),
    (S.T a).obj X = ⟨(A.S.T a).obj X.obj⟩
  transitionTensor : ∀ {E L} (a : E ≤ L), (S.T a).CoreMonoidal
  identity : ∀ E, S.T (le_refl E) ≅ 𝟭 (Rat C E)
  extendedPerfect : ∀ {E L} (a : E ≤ L) (X : Rat C E),
    DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).obj ((F E).obj X))
  kappa : ∀ {E L} (a : E ≤ L),
    DerivedCategory.PerfectScalar.B.{u, u} (fieldMap l Ω a) ≅
      DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom
  phi : ∀ {E L} (a : E ≤ L), S.T a ⋙ F L ≅
    F E ⋙ DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom

/-- Rational comparison condition 1. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition1 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E (X Y : Rat C E), X ⊗ Y = ⟨X.obj ⊗ Y.obj⟩)

/-- Rational comparison condition 2. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition2 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E, (𝟙_ (Rat C E)) = ⟨𝟙_ (C E)⟩)

/-- Rational comparison condition 3. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition3 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E (X X' Y Y' : Rat C E) (f : X.obj ⟶ X'.obj)
    (g : Y.obj ⟶ Y'.obj)
    (a b : Localization.Away (uniformizer l Ω E)),
    HEq (MonoidalCategoryStruct.tensorHom (C := Rat C E)
      (a ⊗ₜ[Integers l Ω E] f : X ⟶ X')
      (b ⊗ₜ[Integers l Ω E] g : Y ⟶ Y'))
      ((a * b) ⊗ₜ[Integers l Ω E] (f ⊗ₘ g) :
        (⟨X.obj ⊗ Y.obj⟩ : Rat C E) ⟶ ⟨X'.obj ⊗ Y'.obj⟩))

/-- Rational comparison condition 4. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition4 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E (X Y Z : Rat C E), HEq (α_ X Y Z).hom
    ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (α_ X.obj Y.obj Z.obj).hom))

/-- Rational comparison condition 5. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition5 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E (X Y : Rat C E), HEq (β_ X Y).hom
    ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (β_ X.obj Y.obj).hom))

/-- Rational comparison condition 6. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition6 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E (X : Rat C E), HEq (λ_ X).hom
    ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (λ_ X.obj).hom))

/-- Rational comparison condition 7. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition7 (A : IntegralData C) [RationalStructures C]
    (_datum : RationalData C A) : Prop :=
  (∀ E (X : Rat C E), HEq (ρ_ X).hom
    ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (ρ_ X.obj).hom))

/-- Rational comparison condition 8. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition8 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E, (datum.F E).Additive)

/-- Rational comparison condition 9. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition9 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E (X Y : Rat C E) (f : X.obj ⟶ Y.obj)
    (a : Localization.Away (uniformizer l Ω E)),
    HEq ((datum.F E).map (a ⊗ₜ[Integers l Ω E] f : X ⟶ Y))
      (coefficientEquiv l Ω E a •
        (fractionB l Ω E).map ((A.F E).map f)))

/-- Rational comparison condition 10. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition10 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E (X Y : Rat C E), HEq ((datum.tensor E).μIso X Y).inv
    ((fractionB l Ω E).map
        ((A.tensor E).μIso X.obj Y.obj).inv ≫
      (scalarTensor (fractionMap l Ω E) _ _ (A.perfect E X.obj) (A.perfect E Y.obj)).hom))

/-- Rational comparison condition 11. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition11 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E, HEq (datum.tensor E).εIso.inv
    ((fractionB l Ω E).map (A.tensor E).εIso.inv ≫
      (scalarUnit (fractionMap l Ω E)).hom))

/-- Rational comparison condition 12. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition12 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E (X Y : Rat C E),
    (datum.F E).map (β_ X Y).hom ≫ ((datum.tensor E).μIso Y X).inv =
      ((datum.tensor E).μIso X Y).inv ≫
        (fieldSymmetry l Ω E ((datum.F E).obj X) ((datum.F E).obj Y)).hom)

/-- Rational comparison condition 13. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition13 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : Rat C E) (f : X.obj ⟶ Y.obj)
    (b : Localization.Away (uniformizer l Ω E)),
    HEq ((datum.S.T a).map (b ⊗ₜ[Integers l Ω E] f : X ⟶ Y))
      ((coefficientEquiv l Ω L).symm
        ((fieldMap l Ω a).hom (coefficientEquiv l Ω E b)) ⊗ₜ[
          Integers l Ω L] (A.S.T a).map f :
            (⟨(A.S.T a).obj X.obj⟩ : Rat C L) ⟶ ⟨(A.S.T a).obj Y.obj⟩))

/-- Rational comparison condition 14. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition14 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L), (datum.S.T a).Additive)

/-- Rational comparison condition 15. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition15 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : Rat C E),
    HEq ((datum.transitionTensor a).μIso X Y).inv
      ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
        Integers l Ω L] ((A.transitionTensor a).μIso X.obj Y.obj).inv))

/-- Rational comparison condition 16. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition16 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L), HEq (datum.transitionTensor a).εIso.inv
    ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
      Integers l Ω L] (A.transitionTensor a).εIso.inv))

/-- Rational comparison condition 17. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition17 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : Rat C E),
    (datum.S.T a).map (β_ X Y).hom ≫ ((datum.transitionTensor a).μIso Y X).inv =
      ((datum.transitionTensor a).μIso X Y).inv ≫
        (β_ ((datum.S.T a).obj X) ((datum.S.T a).obj Y)).hom)

/-- Rational comparison condition 18. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition18 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E (X : Rat C E), HEq ((datum.identity E).hom.app X)
    ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (A.identity E).hom.app X.obj))

/-- Rational comparison condition 19. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition19 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M) (X : Rat C E),
    HEq ((datum.S.assoc a b).hom.app X)
      ((1 : Localization.Away (uniformizer l Ω M)) ⊗ₜ[
        Integers l Ω M] (A.S.assoc a b).hom.app X.obj))

/-- Rational comparison condition 20. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition20 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X : Rat C E),
    (datum.S.assoc (le_refl E) a).hom.app X = (datum.S.T a).map ((datum.identity E).hom.app X))

/-- Rational comparison condition 21. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition21 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X : Rat C E),
    (datum.S.assoc a (le_refl L)).hom.app X = (datum.identity L).hom.app ((datum.S.T a).obj X))

/-- Rational comparison condition 22. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition22 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (P : CochainComplex (ModuleCat.{u} (FieldOf l Ω E)) ℤ),
    (datum.kappa a).hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.extendScalars (fieldMap l Ω a).hom).mapDerivedCategoryFactors.hom.app P =
      DerivedCategory.PerfectScalar.modelMap.{u, u} (fieldMap l Ω a) P)

/-- Rational comparison condition 23. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition23 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X : Rat C E),
    HEq ((datum.F L).map (eqToHom (datum.transitionObject a X)) ≫
        eqToHom (datum.object L ⟨(A.S.T a).obj X.obj⟩) ≫
        (fractionB l Ω L).map ((A.phi a X.obj).hom) ≫
        (scalarComp (integerMap l Ω a) (fractionMap l Ω L) ((A.F E).obj X.obj) (A.perfect E
      X.obj)).hom)
      ((datum.phi a).hom.app X ≫ (datum.kappa a).inv.app ((datum.F E).obj X) ≫
        (DerivedCategory.PerfectScalar.B.{u, u} (fieldMap l Ω a)).map (eqToHom (datum.object E X)) ≫
        (scalarComp (fractionMap l Ω E) (fieldMap l Ω a) ((A.F E).obj X.obj) (A.perfect E
      X.obj)).hom))

/-- Rational comparison condition 24. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition24 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E (X : Rat C E), HEq ((datum.phi (le_refl E)).hom.app X)
    ((datum.F E).map ((datum.identity E).hom.app X) ≫
      (DerivedCategory.fieldScalarUnit (FieldOf l Ω E)).inv.app ((datum.F E).obj X)))

/-- Rational comparison condition 25. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition25 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M) (X : Rat C E),
    HEq ((datum.F M).map ((datum.S.assoc a b).hom.app X) ≫ (datum.phi (a.trans b)).hom.app X)
      ((datum.phi b).hom.app ((datum.S.T a).obj X) ≫
        (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω b).hom).map
          ((datum.phi a).hom.app X) ≫
        (DerivedCategory.fieldScalarTower (fieldMap l Ω a).hom
          (fieldMap l Ω b).hom).hom.app ((datum.F E).obj X)))

/-- Rational comparison condition 26. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition26 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E (X Y : Rat C E),
    ((datum.transitionTensor (le_refl E)).μIso X Y).inv ≫
        ((datum.identity E).hom.app X ⊗ₘ (datum.identity E).hom.app Y) =
      (datum.identity E).hom.app (X ⊗ Y))

/-- Rational comparison condition 27. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition27 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ E,
    (datum.transitionTensor (le_refl E)).εIso.inv = (datum.identity E).hom.app (𝟙_ (Rat C E)))

/-- Rational comparison condition 28. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition28 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M) (X Y : Rat C E),
    (datum.S.T b).map ((datum.transitionTensor a).μIso X Y).inv ≫
        ((datum.transitionTensor b).μIso ((datum.S.T a).obj X) ((datum.S.T a).obj Y)).inv ≫
        ((datum.S.assoc a b).hom.app X ⊗ₘ (datum.S.assoc a b).hom.app Y) =
      (datum.S.assoc a b).hom.app (X ⊗ Y) ≫ ((datum.transitionTensor (a.trans b)).μIso X Y).inv)

/-- Rational comparison condition 29. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition29 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M),
    (datum.S.T b).map (datum.transitionTensor a).εIso.inv ≫ (datum.transitionTensor b).εIso.inv =
      (datum.S.assoc a b).hom.app (𝟙_ (Rat C E)) ≫ (datum.transitionTensor (a.trans b)).εIso.inv)

/-- Rational comparison condition 30. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition30 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : Rat C E),
    (datum.F L).map ((datum.transitionTensor a).μIso X Y).inv ≫
        ((datum.tensor L).μIso ((datum.S.T a).obj X) ((datum.S.T a).obj Y)).inv ≫
        ((datum.phi a).hom.app X ⊗ₘ (datum.phi a).hom.app Y) =
      (datum.phi a).hom.app (X ⊗ Y) ≫
        (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).map
          ((datum.tensor E).μIso X Y).inv ≫
        (datum.kappa a).inv.app ((datum.F E).obj X ⊗ (datum.F E).obj Y) ≫
        (scalarTensor (fieldMap l Ω a) _ _ (datum.perfect E X) (datum.perfect E Y)).hom ≫
        ((datum.kappa a).hom.app ((datum.F E).obj X) ⊗ₘ
          (datum.kappa a).hom.app ((datum.F E).obj Y)))

/-- Rational comparison condition 31. Source: blueprint order 1826
(blueprint: def-sf-rational-tensor-comparison-system). -/
def RationalData.condition31 (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop :=
  (∀ {E L} (a : E ≤ L),
    (datum.F L).map (datum.transitionTensor a).εIso.inv ≫ (datum.tensor L).εIso.inv =
      (datum.phi a).hom.app (𝟙_ (Rat C E)) ≫
        (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).map
          (datum.tensor E).εIso.inv ≫
        (datum.kappa a).inv.app (𝟙_ (D (FieldOf l Ω E))) ≫ (scalarUnit (fieldMap l Ω a)).hom)

/-- All normalized rational object, arrow, tensor, unit, scalar and tower formulas.
Source: blueprint orders 1826 and 1868
(blueprint: def-sf-rational-tensor-comparison-system). -/
structure RationalData.Valid (A : IntegralData C) [RationalStructures C]
    (datum : RationalData C A) : Prop where
  bilinear : ∀ E, ∃ h : MonoidalPreadditive (Rat C E),
    letI := h
    MonoidalLinear (Localization.Away (uniformizer l Ω E)) (Rat C E)
  tensorObject : RationalData.condition1 C A datum
  unitObject : RationalData.condition2 C A datum
  tensorArrow : RationalData.condition3 C A datum
  associator : RationalData.condition4 C A datum
  symmetry : RationalData.condition5 C A datum
  leftUnitor : RationalData.condition6 C A datum
  rightUnitor : RationalData.condition7 C A datum
  additive : RationalData.condition8 C A datum
  arrow : RationalData.condition9 C A datum
  tensorFormula : RationalData.condition10 C A datum
  unitFormula : RationalData.condition11 C A datum
  symmetric : RationalData.condition12 C A datum
  transitionArrow : RationalData.condition13 C A datum
  transitionAdditive : RationalData.condition14 C A datum
  transitionTensor : RationalData.condition15 C A datum
  transitionUnit : RationalData.condition16 C A datum
  transitionSymmetric : RationalData.condition17 C A datum
  identity : RationalData.condition18 C A datum
  tower : RationalData.condition19 C A datum
  leftIdentity : RationalData.condition20 C A datum
  rightIdentity : RationalData.condition21 C A datum
  kappaModel : RationalData.condition22 C A datum
  phiFormula : RationalData.condition23 C A datum
  phiIdentity : RationalData.condition24 C A datum
  phiTower : RationalData.condition25 C A datum
  identityTensor : RationalData.condition26 C A datum
  identityUnit : RationalData.condition27 C A datum
  towerTensor : RationalData.condition28 C A datum
  towerUnit : RationalData.condition29 C A datum
  scalarTensorSquare : RationalData.condition30 C A datum
  scalarUnitSquare : RationalData.condition31 C A datum
end WeilConjectures.TensorComparisonDescent
