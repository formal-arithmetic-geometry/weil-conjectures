/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PointFdQbarCategory
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Tensor comparisons through rationalization and common finite fields

Source: Weil blueprint, main-20261015, order 1826, final coefficient paragraph,
and order 1868; the conditional descent argument of the DAG
(blueprint: def-sf-integral-tensor-comparison-system).

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

/-- Finite fields in the specified algebraic closure. Source: blueprint orders 1826, 1868
(blueprint: def-sf-integral-tensor-comparison-system). -/
abbrev Index := Padic.FiniteCoefficientFields l Ω

/-- The actual finite coefficient field, with a named carrier for instance caching.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
def FieldOf (E : Index l Ω) : Type u := E.val

/-- The existing field structure on that carrier.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
@[instance_reducible] instance fieldOfField (E : Index l Ω) : Field (FieldOf l Ω E) :=
  inferInstanceAs (Field E.val)

/-- The actual coefficient integers, bundled to keep their derived instances small.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
def integerRing (E : Index l Ω) : CommRingCat.{u} :=
  CommRingCat.of (Padic.coefficientExtensionIntegers l E.val)

/-- The carrier of the actual coefficient integers.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
abbrev Integers (E : Index l Ω) := (integerRing l Ω E : Type u)

/-- The existing integer inclusion into its coefficient field.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
@[instance_reducible] instance integerAlgebra (E : Index l Ω) :
    Algebra (Integers l Ω E) (FieldOf l Ω E) :=
  inferInstanceAs (Algebra (Padic.coefficientExtensionIntegers l E.val) E.val)

/-- The recorded uniformizer of the actual coefficient integers.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
def uniformizer (E : Index l Ω) : Integers l Ω E :=
  Padic.coefficientExtensionUniformizer l E.val

/-- The recorded canonical coefficient-field identification on fractions.
Source: blueprint order 1826 (blueprint: def-sf-integral-tensor-comparison-system). -/
def coefficientEquiv (E : Index l Ω) :
    Localization.Away (uniformizer l Ω E) ≃ₐ[Integers l Ω E] (FieldOf l Ω E) :=
  sfRationalCoefficientEquiv l E.val

/-- The coefficient derived category. Source: blueprint orders 1826, 1868
(blueprint: def-sf-integral-tensor-comparison-system). -/
abbrev D (R : Type u) [CommRing R] := DerivedCategory (ModuleCat.{u} R)

/-- The integer inclusion induced by the given field inclusion. Source: order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def integerMap {E L : Index l Ω} (a : E ≤ L) :
    integerRing l Ω E ⟶ integerRing l Ω L :=
  CommRingCat.ofHom (integralScalarIntegerInclusion l E.val L.val
    (IntermediateField.inclusion a))

/-- The integral-to-field coefficient map. Source: blueprint order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def fractionMap (E : Index l Ω) :
    integerRing l Ω E ⟶ CommRingCat.of (FieldOf l Ω E) :=
  CommRingCat.ofHom (algebraMap (Integers l Ω E) (FieldOf l Ω E))

/-- The finite-field inclusion. Source: blueprint orders 1826, 1868
(blueprint: def-sf-integral-tensor-comparison-system). -/
def fieldMap {E L : Index l Ω} (a : E ≤ L) :
    CommRingCat.of (FieldOf l Ω E) ⟶ CommRingCat.of (FieldOf l Ω L) :=
  CommRingCat.ofHom (IntermediateField.inclusion a).toRingHom

/-- Canonical integral scalar extension, with its coefficient categories explicit.
Source: Stacks 06Y6 (blueprint: def-sf-integral-tensor-comparison-system). -/
def integralB {E L : Index l Ω} (a : E ≤ L) : D (Integers l Ω E) ⥤ D (Integers l Ω L) :=
  DerivedCategory.PerfectScalar.B.{u, u} (integerMap l Ω a)

/-- Canonical rational scalar extension, with its coefficient categories explicit.
Source: Stacks 06Y6 (blueprint: def-sf-integral-tensor-comparison-system). -/
def fractionB (E : Index l Ω) : D (Integers l Ω E) ⥤ D (FieldOf l Ω E) :=
  DerivedCategory.PerfectScalar.B.{u, u} (fractionMap l Ω E)

/-- The signed integral tensor symmetry, with its category explicit.
Source: Stacks 0GWN (blueprint: def-sf-integral-tensor-comparison-system). -/
def integralSymmetry (E : Index l Ω) (P Q : D (Integers l Ω E)) : P ⊗ Q ≅ Q ⊗ P :=
  DerivedCategory.PerfectScalar.symmetry.{u, u} (integerRing l Ω E) P Q

/-- The signed field tensor symmetry, with its category explicit.
Source: Stacks 0GWN (blueprint: def-sf-integral-tensor-comparison-system). -/
def fieldSymmetry (E : Index l Ω) (P Q : D (FieldOf l Ω E)) : P ⊗ Q ≅ Q ⊗ P :=
  DerivedCategory.PerfectScalar.symmetry.{u, u} (CommRingCat.of (FieldOf l Ω E)) P Q

/-- The normalized balanced scalar tensorator of the recorded dependency.
Source: Stacks 06Y6, 0GWN (blueprint: def-sf-integral-tensor-comparison-system). -/
def scalarTensor {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D R)
    (hP : DerivedCategory.IsPerfectRingComplex.{u, u} P)
    (hQ : DerivedCategory.IsPerfectRingComplex.{u, u} Q) :=
  DerivedCategory.PerfectScalar.coherenceData.{u, u}.tensor f P Q hP hQ

/-- The normalized scalar unit of the recorded dependency.
Source: Stacks 06Y6 (blueprint: def-sf-integral-tensor-comparison-system). -/
def scalarUnit {R S : CommRingCat.{u}} (f : R ⟶ S) :=
  DerivedCategory.PerfectScalar.coherenceData.{u, u}.unit f

/-- The normalized scalar tower of the recorded dependency.
Source: Stacks 06Y6 (blueprint: def-sf-integral-tensor-comparison-system). -/
def scalarComp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (P : D R)
    (hP : DerivedCategory.IsPerfectRingComplex.{u, u} P) :=
  DerivedCategory.PerfectScalar.coherenceData.{u, u}.comp f g P hP

/-- The normalized scalar identity of the recorded dependency.
Source: Stacks 06Y6 (blueprint: def-sf-integral-tensor-comparison-system). -/
def scalarIdentity (R : CommRingCat.{u}) (P : D R)
    (hP : DerivedCategory.IsPerfectRingComplex.{u, u} P) :=
  DerivedCategory.PerfectScalar.coherenceData.{u, u}.identity R P hP

attribute [irreducible] scalarTensor scalarUnit scalarComp scalarIdentity
attribute [irreducible] integralSymmetry fieldSymmetry integerRing
attribute [irreducible] uniformizer coefficientEquiv FieldOf

variable {l Ω}
  (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear
      (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]

/-- Exactly the integral hypotheses: perfect-valued linear functors, symmetric strong
comparisons, a coherent monoidal transition system, and the scalar tensor/unit squares.
CoreMonoidal supplies naturality, associativity and both unit equations for each functor.
Source: the conditional hypotheses at blueprint order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
structure IntegralData where
  F : ∀ E, C E ⥤ D (Integers l Ω E)
  perfect : ∀ E (X : C E), DerivedCategory.IsPerfectRingComplex.{u, u} ((F E).obj X)
  tensor : ∀ E, (F E).CoreMonoidal
  S : StageSystem C
  transitionTensor : ∀ {E L} (a : E ≤ L), (S.T a).CoreMonoidal
  identity : ∀ E, S.T (le_refl E) ≅ 𝟭 (C E)
  phi : ∀ {E L} (a : E ≤ L) (X : C E),
    (F L).obj ((S.T a).obj X) ≅
      (integralB l Ω a).obj ((F E).obj X)

/-- Integral hypothesis clause 1; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause1 (datum : IntegralData C) : Prop :=
(∀ {E L} (a : E ≤ L) (X Y : C E) (f : X ⟶ Y),
    (datum.F L).map ((datum.S.T a).map f) ≫ (datum.phi a Y).hom =
      (datum.phi a X).hom ≫
        (integralB l Ω a).map ((datum.F E).map f))

/-- Integral hypothesis clause 2; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause2 (datum : IntegralData C) : Prop :=
  (∀ E, (datum.F E).Additive)

/-- Integral hypothesis clause 3; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause3 (datum : IntegralData C) : Prop :=
  (∀ E, (datum.F E).Linear (Integers l Ω E))

/-- Integral hypothesis clause 4; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause4 (datum : IntegralData C) : Prop :=
  (∀ E (X Y : C E),
    (datum.F E).map (β_ X Y).hom ≫ ((datum.tensor E).μIso Y X).inv =
      ((datum.tensor E).μIso X Y).inv ≫
        (integralSymmetry l Ω E ((datum.F E).obj X) ((datum.F E).obj Y)).hom)

/-- Integral hypothesis clause 5; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause5 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L), (datum.S.T a).Additive)

/-- Integral hypothesis clause 6; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause6 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : C E)
    (r : Integers l Ω E) (f : X ⟶ Y),
    (datum.S.T a).map (r • f) = (integerMap l Ω a).hom r • (datum.S.T a).map f)

/-- Integral hypothesis clause 7; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause7 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : C E),
    (datum.S.T a).map (β_ X Y).hom ≫ ((datum.transitionTensor a).μIso Y X).inv =
      ((datum.transitionTensor a).μIso X Y).inv ≫
        (β_ ((datum.S.T a).obj X) ((datum.S.T a).obj Y)).hom)

/-- Integral hypothesis clause 8; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause8 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L) (X : C E),
    (datum.S.assoc (le_refl E) a).hom.app X = (datum.S.T a).map ((datum.identity E).hom.app X))

/-- Integral hypothesis clause 9; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause9 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L) (X : C E),
    (datum.S.assoc a (le_refl L)).hom.app X = (datum.identity L).hom.app ((datum.S.T a).obj X))

/-- Integral hypothesis clause 10; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause10 (datum : IntegralData C) : Prop :=
  (∀ E (X Y : C E),
    ((datum.transitionTensor (le_refl E)).μIso X Y).inv ≫
        ((datum.identity E).hom.app X ⊗ₘ (datum.identity E).hom.app Y) =
      (datum.identity E).hom.app (X ⊗ Y))

/-- Integral hypothesis clause 11; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause11 (datum : IntegralData C) : Prop :=
  (∀ E,
    (datum.transitionTensor (le_refl E)).εIso.inv = (datum.identity E).hom.app (𝟙_ (C E)))

/-- Integral hypothesis clause 12; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause12 (datum : IntegralData C) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M) (X Y : C E),
    (datum.S.T b).map ((datum.transitionTensor a).μIso X Y).inv ≫
        ((datum.transitionTensor b).μIso ((datum.S.T a).obj X) ((datum.S.T a).obj Y)).inv ≫
        ((datum.S.assoc a b).hom.app X ⊗ₘ (datum.S.assoc a b).hom.app Y) =
      (datum.S.assoc a b).hom.app (X ⊗ Y) ≫ ((datum.transitionTensor (a.trans b)).μIso X Y).inv)

/-- Integral hypothesis clause 13; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause13 (datum : IntegralData C) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M),
    (datum.S.T b).map (datum.transitionTensor a).εIso.inv ≫ (datum.transitionTensor b).εIso.inv =
      (datum.S.assoc a b).hom.app (𝟙_ (C E)) ≫ (datum.transitionTensor (a.trans b)).εIso.inv)

/-- Integral hypothesis clause 14; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause14 (datum : IntegralData C) : Prop :=
  (∀ E (X : C E), HEq ((datum.phi (le_refl E) X).hom)
    ((datum.F E).map ((datum.identity E).hom.app X) ≫
      (scalarIdentity (integerRing l Ω E) ((datum.F E).obj X) (datum.perfect E X)).inv))

/-- Integral hypothesis clause 15; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause15 (datum : IntegralData C) : Prop :=
  (∀ {E L M} (a : E ≤ L) (b : L ≤ M) (X : C E),
    HEq ((datum.F M).map ((datum.S.assoc a b).hom.app X) ≫ (datum.phi (a.trans b) X).hom)
      ((datum.phi b ((datum.S.T a).obj X)).hom ≫
        (integralB l Ω b).map ((datum.phi a X).hom) ≫
        (scalarComp (integerMap l Ω a) (integerMap l Ω b)
          ((datum.F E).obj X) (datum.perfect E X)).hom))

/-- Integral hypothesis clause 16; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause16 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L) (X Y : C E),
    (datum.F L).map ((datum.transitionTensor a).μIso X Y).inv ≫
        ((datum.tensor L).μIso ((datum.S.T a).obj X) ((datum.S.T a).obj Y)).inv ≫
        ((datum.phi a X).hom ⊗ₘ (datum.phi a Y).hom) =
      (datum.phi a (X ⊗ Y)).hom ≫
        (integralB l Ω a).map
          ((datum.tensor E).μIso X Y).inv ≫
        (scalarTensor (integerMap l Ω a) _ _ (datum.perfect E X) (datum.perfect E Y)).hom)

/-- Integral hypothesis clause 17; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
def IntegralData.clause17 (datum : IntegralData C) : Prop :=
  (∀ {E L} (a : E ≤ L),
    (datum.F L).map (datum.transitionTensor a).εIso.inv ≫ (datum.tensor L).εIso.inv =
      (datum.phi a (𝟙_ (C E))).hom ≫
        (integralB l Ω a).map (datum.tensor E).εIso.inv ≫
        (scalarUnit (integerMap l Ω a)).hom)

/-- All integral hypothesis clauses; source: conditional descent, order 1826
(blueprint: def-sf-integral-tensor-comparison-system). -/
structure IntegralData.Valid (datum : IntegralData C) : Prop where
  finiteBiproducts : (∀ E, CategoryTheory.Limits.HasFiniteBiproducts (C E))
  hypothesis1 : datum.clause1
  hypothesis2 : datum.clause2
  hypothesis3 : datum.clause3
  hypothesis4 : datum.clause4
  hypothesis5 : datum.clause5
  hypothesis6 : datum.clause6
  hypothesis7 : datum.clause7
  hypothesis8 : datum.clause8
  hypothesis9 : datum.clause9
  hypothesis10 : datum.clause10
  hypothesis11 : datum.clause11
  hypothesis12 : datum.clause12
  hypothesis13 : datum.clause13
  hypothesis14 : datum.clause14
  hypothesis15 : datum.clause15
  hypothesis16 : datum.clause16
  hypothesis17 : datum.clause17


end WeilConjectures.TensorComparisonDescent
