/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.CategoryTheory.Functor.Currying
public import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Bilinear comparisons under coefficient descent

Source: main-20261015, `def-weil-rationalization-karoubi` (raw Hom tensor formula)
and `def-weil-algebraically-closed-coefficients` (common-stage Hom formula).
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).

The algebraic and common-stage assertions are parametrized separately: the latter applies
both before and after the former, and does not assume additive objects or triangulations.
Scalar-first tensors use the recorded ScalarLocalization convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] CategoryTheory.Prod.sectL CategoryTheory.Prod.sectR
  CategoryTheory.ScalarLocalization.extension
attribute [local instance 2000] DivisionSemiring.to_moduleIsTorsionFree

set_option linter.unusedSectionVars false

universe r u v u' v' u₂ v₂ u₃ v₃ w

open CategoryTheory TensorProduct

namespace CategoryTheory.BilinearCoefficientDescent

variable {R : Type r} [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]

/-- Separate linearity includes additivity in each variable. Source: raw Hom tensor formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsSeparatelyLinear (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    (U : C × C ⥤ D) : Prop where
  right :
    ∀ X : C, (Prod.sectR X C ⋙ U).Additive ∧ (Prod.sectR X C ⋙ U).Linear R
  left :
    ∀ Y : C, (Prod.sectL C Y ⋙ U).Additive ∧ (Prod.sectL C Y ⋙ U).Linear R

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isSeparatelyLinear_iff (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    (U : C × C ⥤ D) :
    IsSeparatelyLinear R U ↔
  (∀ X : C, (Prod.sectR X C ⋙ U).Additive ∧ (Prod.sectR X C ⋙ U).Linear R) ∧
  (∀ Y : C, (Prod.sectL C Y ⋙ U).Additive ∧ (Prod.sectL C Y ⋙ U).Linear R) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

/-- The exact object and pure-tensor prescriptions for an extension. Source: raw Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsRawExtension (p : R) (U : C × C ⥤ D)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p) : Prop where
  linear :
    IsSeparatelyLinear (Localization.Away p) F
  formula :
      (∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
      F.obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩) ∧
    ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') (a b : Localization.Away p),
      HEq (F.map (X := (⟨X⟩, ⟨Y⟩)) (Y := (⟨X'⟩, ⟨Y'⟩))
        (a ⊗ₜ[R] f, b ⊗ₜ[R] g)) ((a * b) ⊗ₜ[R] U.map (X := (X, Y)) (Y := (X', Y')) (f, g))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isRawExtension_iff (p : R) (U : C × C ⥤ D)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p) :
    IsRawExtension p U F ↔
  IsSeparatelyLinear (Localization.Away p) F ∧
  (∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
    F.obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩) ∧
  ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') (a b : Localization.Away p),
    HEq (F.map (X := (⟨X⟩, ⟨Y⟩)) (Y := (⟨X'⟩, ⟨Y'⟩))
      (a ⊗ₜ[R] f, b ⊗ₜ[R] g)) ((a * b) ⊗ₜ[R] U.map (X := (X, Y)) (Y := (X', Y')) (f, g)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

@[no_expose] private def tensorComp (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M)) (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    Localization.Away p ⊗[R] (K ⟶ M) :=
  ((ScalarLocalization.composition R C p K L M).toFun g).toFun f

attribute [local implicit_reducible] tensorComp

private theorem tensorComp_zero_left (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    tensorComp R C p K L M 0 f = 0 := by
  exact congrArg (fun k ↦ k f) (ScalarLocalization.composition R C p K L M).map_zero

private theorem tensorComp_zero_right (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M)) :
    tensorComp R C p K L M g 0 = 0 := by
  exact ((ScalarLocalization.composition R C p K L M) g).map_zero

private theorem tensorComp_add_left (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g g' : Localization.Away p ⊗[R] (L ⟶ M))
    (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    tensorComp R C p K L M (g + g') f =
      tensorComp R C p K L M g f + tensorComp R C p K L M g' f := by
  exact congrArg (fun k ↦ k f) ((ScalarLocalization.composition R C p K L M).map_add g g')

private theorem tensorComp_add_right (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M))
    (f f' : Localization.Away p ⊗[R] (K ⟶ L)) :
    tensorComp R C p K L M g (f + f') =
      tensorComp R C p K L M g f + tensorComp R C p K L M g f' := by
  exact ((ScalarLocalization.composition R C p K L M) g).map_add f f'

private theorem tensorComp_tmul (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p) :
    tensorComp R C p K L M (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f) := by
  exact ScalarLocalization.composition_tmul R C p K L M f g a b

attribute [local simp] tensorComp_zero_left tensorComp_zero_right
  tensorComp_add_left tensorComp_add_right

private theorem hom_add_heq {E : Type u₃} [Category.{v₃} E] [Preadditive E]
    {X Y X' Y' : E} (hx : X = X') (hy : Y = Y')
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} (hf : HEq f f') (hg : HEq g g') :
    HEq (f + g) (f' + g') := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hf) (eq_of_heq hg))

@[no_expose] private def integralHom (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (X X' Y Y' : C) : (X ⟶ X') →ₗ[R] (Y ⟶ Y') →ₗ[R]
      (U.obj (X, Y) ⟶ U.obj (X', Y')) := by
  letI := (hU.1 X').1
  letI := (hU.1 X').2
  letI := (hU.2 Y).1
  letI := (hU.2 Y).2
  exact LinearMap.mk₂ R
    (fun f g ↦ ((Prod.sectL C Y ⋙ U).map f) ≫ ((Prod.sectR X' C ⋙ U).map g))
    (by intros; rw [(Prod.sectL C Y ⋙ U).map_add, Preadditive.add_comp])
    (by intros; rw [(Prod.sectL C Y ⋙ U).map_smul, Linear.smul_comp])
    (by intros; rw [(Prod.sectR X' C ⋙ U).map_add, Preadditive.comp_add])
    (by intros; rw [(Prod.sectR X' C ⋙ U).map_smul, Linear.comp_smul])

private theorem integralHom_apply (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    integralHom U hU X X' Y Y' f g =
      U.map (X := (X, Y)) (Y := (X', Y')) (f, g) := by
  change U.map (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) ≫
    U.map (X := (X', Y)) (Y := (X', Y')) (𝟙 X', g) =
      U.map (X := (X, Y)) (Y := (X', Y')) (f, g)
  rw [← U.map_comp]
  congr 1
  exact Prod.ext (Category.comp_id f) (Category.id_comp g)

attribute [local irreducible] integralHom

@[no_expose] private noncomputable def rawHomLinear (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C) :
    (Localization.Away p ⊗[R] (X ⟶ X')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (Y ⟶ Y')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (U.obj (X, Y) ⟶ U.obj (X', Y'))) :=
  TensorProduct.curry
    (((TensorProduct.lift (integralHom U hU X X' Y Y')).baseChange
      (Localization.Away p)).comp
        (AlgebraTensorModule.distribBaseChange R (Localization.Away p)
          (X ⟶ X') (Y ⟶ Y')).symm.toLinearMap)

@[no_expose] private def rawHom (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    Localization.Away p ⊗[R] (U.obj (X, Y) ⟶ U.obj (X', Y')) :=
  ((rawHomLinear p U hU X X' Y Y').toFun f).toFun g

private theorem rawHom_tmul (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) {X X' Y Y' : C}
    (a b : Localization.Away p) (f : X ⟶ X') (g : Y ⟶ Y') :
    rawHom p U hU X X' Y Y' (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) =
      (a * b) ⊗ₜ[R] U.map (f, g) := by
  change rawHomLinear p U hU X X' Y Y' (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = _
  simp only [rawHomLinear, TensorProduct.curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.distribBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    TensorProduct.lift.tmul, integralHom_apply]

private theorem rawHom_zero_left (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' 0 g = 0 := by
  exact congrArg (fun k ↦ k g) (rawHomLinear p U hU X X' Y Y').map_zero

private theorem rawHom_zero_right (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X')) :
    rawHom p U hU X X' Y Y' f 0 = 0 := by
  exact ((rawHomLinear p U hU X X' Y Y') f).map_zero

private theorem rawHom_add_left (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f f' : Localization.Away p ⊗[R] (X ⟶ X')) (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' (f + f') g =
      rawHom p U hU X X' Y Y' f g + rawHom p U hU X X' Y Y' f' g := by
  exact congrArg (fun k ↦ k g) ((rawHomLinear p U hU X X' Y Y').map_add f f')

private theorem rawHom_add_right (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X')) (g g' : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' f (g + g') =
      rawHom p U hU X X' Y Y' f g + rawHom p U hU X X' Y Y' f g' := by
  exact ((rawHomLinear p U hU X X' Y Y') f).map_add g g'

private theorem rawHom_smul_left (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (a : Localization.Away p)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' (a • f) g = a • rawHom p U hU X X' Y Y' f g := by
  exact congrArg (fun k ↦ k g) ((rawHomLinear p U hU X X' Y Y').map_smul a f)

private theorem rawHom_smul_right (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (a : Localization.Away p)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' f (a • g) = a • rawHom p U hU X X' Y Y' f g := by
  exact ((rawHomLinear p U hU X X' Y Y') f).map_smul a g

attribute [local simp] rawHom_zero_left rawHom_zero_right rawHom_add_left rawHom_add_right

attribute [local irreducible] rawHom rawHomLinear ScalarLocalization.composition
  ScalarLocalization.extensionHom ScalarLocalization.coefficientMap

private theorem rawHom_comp (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' X'' Y Y' Y'' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (f' : Localization.Away p ⊗[R] (X' ⟶ X''))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y'))
    (g' : Localization.Away p ⊗[R] (Y' ⟶ Y'')) :
    rawHom p U hU X X'' Y Y''
        (tensorComp R C p X X' X'' f' f)
        (tensorComp R C p Y Y' Y'' g' g) =
      tensorComp R D p _ _ _
        (rawHom p U hU X' X'' Y' Y'' f' g') (rawHom p U hU X X' Y Y' f g) := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [tensorComp_zero_right, rawHom_zero_left]
  | add f f₁ hf hf₁ => simp only [tensorComp_add_right, rawHom_add_left,
    hf, hf₁]
  | tmul a f =>
    induction f' using TensorProduct.induction_on with
    | zero => simp only [tensorComp_zero_left, rawHom_zero_left]
    | add f' f₁ hf hf₁ => simp only [tensorComp_add_left, rawHom_add_left,
      hf, hf₁]
    | tmul a' f' =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [tensorComp_zero_right, rawHom_zero_right]
      | add g g₁ hg hg₁ => simp only [tensorComp_add_right, rawHom_add_right,
        hg, hg₁]
      | tmul b g =>
        induction g' using TensorProduct.induction_on with
        | zero => simp only [tensorComp_zero_left, rawHom_zero_right]
        | add g' g₁ hg hg₁ => simp only [tensorComp_add_left,
          rawHom_add_right,
          hg, hg₁]
        | tmul b' g' =>
          simp only [tensorComp_tmul, rawHom_tmul]
          rw [← U.map_comp]
          congr 1
          ac_rfl

@[no_expose] private noncomputable def rawFunctor (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) :
    ScalarLocalization R C p × ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨U.obj (X.1.obj, X.2.obj)⟩
  map {X Y} f := rawHom p U hU _ _ _ _ f.1 f.2
  map_id X := by
    change rawHom p U hU _ _ _ _ (1 ⊗ₜ[R] 𝟙 _) (1 ⊗ₜ[R] 𝟙 _) = _
    rw [rawHom_tmul, one_mul]
    exact congrArg (fun f ↦ (1 : Localization.Away p) ⊗ₜ[R] f) (U.map_id _)
  map_comp {X Y Z} f g := rawHom_comp p U hU _ _ _ _ _ _ f.1 g.1 f.2 g.2

attribute [local implicit_reducible] rawFunctor

private theorem rawFunctor_linear (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) : IsSeparatelyLinear (Localization.Away p)
      (rawFunctor p U hU) := by
  constructor
  · intro X
    constructor
    · constructor
      intro Y Y' f g
      exact rawHom_add_right p U hU _ _ _ _ (𝟙 X) f g
    · constructor
      intro Y Y' f a
      exact rawHom_smul_right p U hU _ _ _ _ a (𝟙 X) f
  · intro Y
    constructor
    · constructor
      intro X X' f g
      exact rawHom_add_left p U hU _ _ _ _ f g (𝟙 Y)
    · constructor
      intro X X' f a
      exact rawHom_smul_left p U hU _ _ _ _ a f (𝟙 Y)

/-- Unique raw bilinear extension, including torsion Hom modules.
Source: raw Hom tensor formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 1--2: factor U(f,g) as U(f,1) followed by U(1,g). Separate linearity and
bilinear composition make this bilinear on the two Hom modules. Apply module base change
(def-weil-module-base-change). On pure tensors identity and composition are the integral
functor laws times the product of scalars. Tensor induction gives the laws and uniqueness;
no injectivity into the tensor product is used. -/
theorem raw_extension_existsUnique (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) :
    ∃! F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p, IsRawExtension p U F := by
  refine ⟨rawFunctor p U hU, ⟨rawFunctor_linear p U hU, fun _ ↦ rfl, ?_⟩, ?_⟩
  · intro X X' Y Y' f g a b
    exact heq_of_eq (rawHom_tmul p U hU a b f g)
  · intro F hF
    apply Functor.hext hF.2.1
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ f
    let X := (X₁, X₂)
    let Y := (Y₁, Y₂)
    have hh (f₁ : X.1 ⟶ Y.1) (f₂ : X.2 ⟶ Y.2) :
        HEq (integralHom F hF.1 X.1 Y.1 X.2 Y.2 f₁ f₂)
          (rawHom p U hU _ _ _ _ f₁ f₂) := by
      induction f₁ using TensorProduct.induction_on with
      | zero =>
        apply (conj_eqToHom_iff_heq _ _ (hF.2.1 X) (hF.2.1 Y)).1
        simp
      | tmul a f₁ =>
        induction f₂ using TensorProduct.induction_on with
        | zero =>
          apply (conj_eqToHom_iff_heq _ _ (hF.2.1 X) (hF.2.1 Y)).1
          simp
        | tmul b f₂ =>
          rw [integralHom_apply, rawHom_tmul]
          exact hF.2.2 _ _ _ _ f₁ f₂ a b
        | add g h hg hh =>
          rw [LinearMap.map_add, rawHom_add_right]
          exact hom_add_heq (hF.2.1 X) (hF.2.1 Y) hg hh
      | add g h hg hh =>
        simp only [rawHom_add_left, LinearMap.map_add,
          LinearMap.add_apply]
        exact hom_add_heq (hF.2.1 X) (hF.2.1 Y) hg hh
    rcases f with ⟨f, g⟩
    simpa only [integralHom_apply, X, Y, rawFunctor] using hh f g

/-- Give a functor its prescribed object function, transporting its morphisms.
Source: transport along object equalities
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def withObjects
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) : C₀ ⥤ D₀ where
  obj := obj
  map {X Y} f := eqToHom (h X).symm ≫ F.map f ≫ eqToHom (h Y)
  map_id X := by
    simp only [F.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
  map_comp f g := by
    simp only [F.map_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

/-- Object normalization preserves the functor itself.
Source: equality of functors by object equality and heterogeneous map equality
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem withObjects_eq
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) :
    withObjects F obj h = F := by
  unfold withObjects
  apply Functor.hext (fun X ↦ (h X).symm)
  intro X Y f
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The unique raw extension; all its data are determined by the preceding prescription.
Source: raw Hom tensor formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def raw (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :=
  withObjects (raw_extension_existsUnique p U hU).exists.choose
    (fun X ↦ ⟨U.obj (X.1.obj, X.2.obj)⟩)
    (raw_extension_existsUnique p U hU).exists.choose_spec.2.1

/-- The chosen raw functor satisfies the full extension prescription.
Source: the proved unique extension
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem raw_spec (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :
    IsRawExtension p U (raw p U hU) := by
  unfold raw
  rw [withObjects_eq]
  exact (raw_extension_existsUnique p U hU).exists.choose_spec

/-- The raw extension retains the stipulated object.
Source: the uniquely prescribed construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem raw_obj (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X : ScalarLocalization R C p × ScalarLocalization R C p) :
    (raw p U hU).obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩ := by
  exact Eq.trans rfl rfl

private theorem id_heq {E : Type*} [Category E] {X Y : E} (h : X = Y) :
    HEq (𝟙 X) (𝟙 Y) := by
  subst Y
  rfl

private theorem raw_eq (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :
    raw p U hU = rawFunctor p U hU := by
  apply (raw_extension_existsUnique p U hU).unique
  · exact raw_spec p U hU
  · refine ⟨rawFunctor_linear p U hU, fun _ ↦ rfl, ?_⟩
    intro X X' Y Y' f g a b
    exact heq_of_eq (rawHom_tmul p U hU a b f g)

@[no_expose] private def rawNat (p : R) (U V : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V) (η : U ⟶ V) :
    rawFunctor p U hU ⟶ rawFunctor p V hV where
  app X := (1 : Localization.Away p) ⊗ₜ[R] η.app (X.1.obj, X.2.obj)
  naturality {X Y} f := by
    change tensorComp R D p _ _ _ (1 ⊗ₜ[R] η.app _)
      (rawHom p U hU _ _ _ _ f.1 f.2) =
      tensorComp R D p _ _ _ (rawHom p V hV _ _ _ _ f.1 f.2)
        (1 ⊗ₜ[R] η.app _)
    rcases f with ⟨f, g⟩
    induction f using TensorProduct.induction_on with
    | zero => simp only [tensorComp_zero_left, tensorComp_zero_right, rawHom_zero_left]
    | add f f' hf hf' => simp only [tensorComp_add_left, tensorComp_add_right, rawHom_add_left,
      hf, hf']
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [tensorComp_zero_left, tensorComp_zero_right, rawHom_zero_right]
      | add g g' hg hg' => simp only [tensorComp_add_left, tensorComp_add_right, rawHom_add_right,
        hg, hg']
      | tmul b g =>
        simp only [rawHom_tmul, tensorComp_tmul, one_mul, mul_one,
          η.naturality]

/-- Extension of arbitrary transformation components, needed for equation descent.
Source: raw Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 3 and 12: tensor the naturality equation with the product of the two scalars,
then use tensor induction. The unchanged objects make the component prescription unique. -/
theorem raw_transformation_existsUnique (p : R) (U V : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V) (η : U ⟶ V) :
    ∃! e : raw p U hU ⟶ raw p V hV,
      ∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
        HEq (e.app X) ((1 : Localization.Away p) ⊗ₜ[R] η.app (X.1.obj, X.2.obj)) := by
  rw [raw_eq p U hU, raw_eq p V hV]
  refine ⟨rawNat p U V hU hV η, fun _ ↦ HEq.rfl, ?_⟩
  intro e he
  apply NatTrans.ext
  funext X
  exact eq_of_heq (he X)

/-- The component-normalized raw transformation. Source: raw Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def rawTransformation (p : R) (U V : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V) (η : U ⟶ V) :=
  (raw_transformation_existsUnique p U V hU hV η).exists.choose

/-- The chosen raw transformation has its pure-tensor component.
Source: the uniquely prescribed construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem rawTransformation_app (p : R) (U V : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V) (η : U ⟶ V)
    (X : ScalarLocalization R C p × ScalarLocalization R C p) :
    HEq ((rawTransformation p U V hU hV η).app X)
      ((1 : Localization.Away p) ⊗ₜ[R] η.app (X.1.obj, X.2.obj)) :=
  (raw_transformation_existsUnique p U V hU hV η).exists.choose_spec X

attribute [local irreducible] raw rawTransformation

/-- Identity and vertical composition are preserved at raw rational stages.
Source: raw Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 12: Q(id) is id, and Q(ηθ) is Q(η)Q(θ) by the pure-tensor composition law.
Transformation extensionality proves both equalities. -/
theorem raw_equations (p : R) :
    (∀ (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U),
      rawTransformation p U U hU hU (𝟙 U) = 𝟙 _) ∧
    (∀ (U V W : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
      (hV : IsSeparatelyLinear R V) (hW : IsSeparatelyLinear R W)
      (η : U ⟶ V) (θ : V ⟶ W),
      rawTransformation p U W hU hW (η ≫ θ) =
        rawTransformation p U V hU hV η ≫ rawTransformation p V W hV hW θ) := by
  constructor
  · intro U hU
    apply NatTrans.ext
    funext X
    exact eq_of_heq ((rawTransformation_app p U U hU hU (𝟙 U) X).trans
      (id_heq (raw_obj p U hU X)).symm)
  · intro U V W hU hV hW η θ
    apply NatTrans.ext
    funext X
    apply eq_of_heq
    apply (rawTransformation_app p U W hU hW (η ≫ θ) X).trans
    have hh := heq_comp (raw_obj p U hU X) (raw_obj p V hV X) (raw_obj p W hW X)
      (rawTransformation_app p U V hU hV η X)
      (rawTransformation_app p V W hV hW θ X)
    apply HEq.trans ?_ hh.symm
    apply heq_of_eq
    change (1 : Localization.Away p) ⊗ₜ[R] (η.app _ ≫ θ.app _) =
      tensorComp R D p _ _ _ (1 ⊗ₜ[R] θ.app _) (1 ⊗ₜ[R] η.app _)
    simp only [tensorComp_tmul, one_mul]

/-- Localized components and inverse components determine the extended natural isomorphism.
Source: raw Hom tensor formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 3: on a pair of pure tensors, naturality is the integral naturality equality
multiplied by ab. Extend by additivity. The inverse identities are the integral inverse
identities tensored with one. The object equalities only transport the unchanged endpoints. -/
theorem raw_comparison (p : R) (U V : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V) (η : U ≅ V) :
    ∃! e : raw p U hU ≅ raw p V hV,
      ∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
        HEq (e.hom.app X) ((1 : Localization.Away p) ⊗ₜ[R] η.hom.app (X.1.obj, X.2.obj)) ∧
        HEq (e.inv.app X) ((1 : Localization.Away p) ⊗ₜ[R] η.inv.app (X.1.obj, X.2.obj)) := by
  let e : raw p U hU ≅ raw p V hV :=
    ⟨rawTransformation p U V hU hV η.hom, rawTransformation p V U hV hU η.inv,
      by rw [← (raw_equations p).2 U V U hU hV hU, η.hom_inv_id,
        (raw_equations p).1],
      by rw [← (raw_equations p).2 V U V hV hU hV, η.inv_hom_id,
        (raw_equations p).1]⟩
  refine ⟨e, ?_, ?_⟩
  · intro X
    exact ⟨rawTransformation_app p U V hU hV η.hom X,
      rawTransformation_app p V U hV hU η.inv X⟩
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext X
    exact eq_of_heq ((he' X).1.trans
      (rawTransformation_app p U V hU hV η.hom X).symm)

private theorem extension_tmul {S' : Type u₃} [CommRing S']
    {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear S' E]
    (p : R) (q : S') (φ : R →+* S')
    (h : IsUnit (algebraMap S' (Localization.Away q) (φ p)))
    (F : C ⥤ E) [F.Additive] (hF : ScalarLocalization.IsSemilinear φ F)
    {X Y : C} (a : Localization.Away p) (f : X ⟶ Y) :
    (ScalarLocalization.extension p q φ h F hF).map
        (X := ⟨X⟩) (Y := ⟨Y⟩) (a ⊗ₜ[R] f) =
      ScalarLocalization.coefficientMap p q φ h a ⊗ₜ[S'] F.map f :=
  by
    unfold ScalarLocalization.extension ScalarLocalization.extensionHom
    exact (ScalarLocalization.existsUnique_semilinearHom p q φ h F hF X Y).exists.choose_spec a f

omit [Linear R D] in
private theorem extendedHom_tmul {S' : Type u₃} [CommRing S'] [Linear S' D]
    (p : R) (q : S') (φ : R →+* S')
    (h : IsUnit (algebraMap S' (Localization.Away q) (φ p)))
    (F : C ⥤ D) [F.Additive] (hF : ScalarLocalization.IsSemilinear φ F)
    (X Y : C) (a : Localization.Away p) (f : X ⟶ Y) :
    ScalarLocalization.extensionHom p q φ h F hF X Y (a ⊗ₜ[R] f) =
      ScalarLocalization.coefficientMap p q φ h a ⊗ₜ[S'] F.map f :=
  by
    unfold ScalarLocalization.extensionHom
    exact (ScalarLocalization.existsUnique_semilinearHom p q φ h F hF X Y).exists.choose_spec a f

section RawWhiskering

variable {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear R E]

private theorem coefficientMap_id (p : R) :
    ScalarLocalization.coefficientMap p p (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit p) = RingHom.id (Localization.Away p) := by
  symm
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
  rfl

private theorem rawHom_output (p : R) (F : D ⥤ E) [F.Additive]
    (hF : ScalarLocalization.IsSemilinear (RingHom.id R) F)
    (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (hFU : IsSeparatelyLinear R (U ⋙ F)) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    ScalarLocalization.extensionHom p p (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit p) F hF (U.obj (X, Y)) (U.obj (X', Y'))
      (rawHom p U hU X X' Y Y' f g) = rawHom p (U ⋙ F) hFU X X' Y Y' f g := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [rawHom_zero_left,
    AddMonoidHom.map_zero]
  | add f f' hf hf' => simp only [rawHom_add_left,
    AddMonoidHom.map_add, hf, hf']
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp only [rawHom_zero_right,
      AddMonoidHom.map_zero]
    | add g g' hg hg' => simp only [rawHom_add_right,
      AddMonoidHom.map_add, hg, hg']
    | tmul b g =>
      rw [rawHom_tmul, extendedHom_tmul, rawHom_tmul, coefficientMap_id]
      rfl

private theorem rawHom_input (p : R) (F G : E ⥤ C) [F.Additive] [G.Additive]
    (hF : ScalarLocalization.IsSemilinear (RingHom.id R) F)
    (hG : ScalarLocalization.IsSemilinear (RingHom.id R) G)
    (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (hUF : IsSeparatelyLinear R (F.prod G ⋙ U)) (X X' Y Y' : E)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU (F.obj X) (F.obj X') (G.obj Y) (G.obj Y')
      (ScalarLocalization.extensionHom p p (RingHom.id R)
        (IsLocalization.Away.algebraMap_isUnit p) F hF X X' f)
      (ScalarLocalization.extensionHom p p (RingHom.id R)
        (IsLocalization.Away.algebraMap_isUnit p) G hG Y Y' g) =
      rawHom p (F.prod G ⋙ U) hUF X X' Y Y' f g := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [rawHom_zero_left,
    AddMonoidHom.map_zero]
  | add f f' hf hf' => simp only [rawHom_add_left,
    AddMonoidHom.map_add, hf, hf']
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp only [rawHom_zero_right,
      AddMonoidHom.map_zero]
    | add g g' hg hg' => simp only [rawHom_add_right,
      AddMonoidHom.map_add, hg, hg']
    | tmul b g =>
      rw [extendedHom_tmul, extendedHom_tmul, rawHom_tmul, rawHom_tmul, coefficientMap_id]
      rfl

private theorem raw_output_eq (p : R) (F : D ⥤ E) [F.Additive]
    (hF : ScalarLocalization.IsSemilinear (RingHom.id R) F)
    (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (hFU : IsSeparatelyLinear R (U ⋙ F)) :
    raw p U hU ⋙ ScalarLocalization.extension p p (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit p) F hF = raw p (U ⋙ F) hFU := by
  rw [raw_eq, raw_eq]
  refine Functor.ext (F := _) (G := rawFunctor p _ _) (fun _ ↦ rfl) ?_
  rintro ⟨⟨X⟩, ⟨Y⟩⟩ ⟨⟨X'⟩, ⟨Y'⟩⟩ ⟨f, g⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact rawHom_output p F hF U hU hFU X X' Y Y' f g

omit [Preadditive D] in
private theorem map_heq {D₀ : Type u₃} [Category.{v₃} D₀]
    (F : D ⥤ D₀) {X Y X' Y' : D} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

/-- Output whiskering of a raw comparison by a scalar-linear functor.
Source: raw Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 12: the extended functor maps a component 1 tensor η to 1 tensor F(η).
Both output functors have the same object and pure-tensor prescriptions, hence agree
under the identity-on-objects comparison. The component formulas prove the square. -/
theorem raw_whisker_output (p : R) (F : D ⥤ E) [F.Additive]
    (hF : ScalarLocalization.IsSemilinear (RingHom.id R) F)
    (U V : C × C ⥤ D) (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V)
    (hFU : IsSeparatelyLinear R (U ⋙ F)) (hFV : IsSeparatelyLinear R (V ⋙ F))
    (η : U ⟶ V) :
    ∃ (eU : raw p U hU ⋙ ScalarLocalization.extension p p (RingHom.id R)
          (IsLocalization.Away.algebraMap_isUnit p) F hF ≅ raw p (U ⋙ F) hFU)
      (eV : raw p V hV ⋙ ScalarLocalization.extension p p (RingHom.id R)
          (IsLocalization.Away.algebraMap_isUnit p) F hF ≅ raw p (V ⋙ F) hFV),
      (∀ X, HEq (eU.hom.app X) (𝟙 ((raw p (U ⋙ F) hFU).obj X)) ∧
        HEq (eV.hom.app X) (𝟙 ((raw p (V ⋙ F) hFV).obj X))) ∧
      Functor.whiskerRight (rawTransformation p U V hU hV η)
          (ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) F hF) ≫ eV.hom =
        eU.hom ≫ rawTransformation p (U ⋙ F) (V ⋙ F) hFU hFV
          (Functor.whiskerRight η F) := by
  let eU := eqToIso (raw_output_eq p F hF U hU hFU)
  let eV := eqToIso (raw_output_eq p F hF V hV hFV)
  refine ⟨eU, eV, ?_, ?_⟩
  · intro X
    constructor <;> dsimp only [eU, eV, eqToIso] <;> rw [eqToHom_app] <;>
      exact eqToHom_heq_id_cod _ _ _
  · apply NatTrans.ext
    funext X
    apply eq_of_heq
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, eU, eV, eqToIso]
    rw [eqToHom_app, eqToHom_app]
    refine (comp_eqToHom_heq _ _).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    have he := map_heq
      (ScalarLocalization.extension p p (RingHom.id R)
        (IsLocalization.Away.algebraMap_isUnit p) F hF)
      (raw_obj p U hU X) (raw_obj p V hV X)
      (rawTransformation_app p U V hU hV η X)
    refine he.trans ?_
    rw [extension_tmul, map_one]
    exact (rawTransformation_app p (U ⋙ F) (V ⋙ F) hFU hFV
      (Functor.whiskerRight η F) X).symm

private theorem raw_input_eq (p : R) (F G : E ⥤ C) [F.Additive] [G.Additive]
    (hF : ScalarLocalization.IsSemilinear (RingHom.id R) F)
    (hG : ScalarLocalization.IsSemilinear (RingHom.id R) G)
    (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (hUF : IsSeparatelyLinear R (F.prod G ⋙ U)) :
    (ScalarLocalization.extension p p (RingHom.id R)
        (IsLocalization.Away.algebraMap_isUnit p) F hF).prod
      (ScalarLocalization.extension p p (RingHom.id R)
        (IsLocalization.Away.algebraMap_isUnit p) G hG) ⋙ raw p U hU =
      raw p (F.prod G ⋙ U) hUF := by
  rw [raw_eq, raw_eq]
  refine Functor.ext (F := _) (G := rawFunctor p _ _) (fun _ ↦ rfl) ?_
  rintro ⟨⟨X⟩, ⟨Y⟩⟩ ⟨⟨X'⟩, ⟨Y'⟩⟩ ⟨f, g⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact rawHom_input p F G hF hG U hU hUF X X' Y Y' f g

/-- Simultaneous input whiskering includes each slot separately by setting one functor to id.
Source: raw Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 12: on a pure tensor input the two constructions are 1 tensor the same
integral component. On arbitrary arrows tensor induction gives the same functor maps;
the object maps coincide. Thus the identity component comparisons are natural and the
transformation square follows componentwise. This applies to each linear partial functor
of a separately linear bifunctor, with its unchanged arguments carried as parameters. -/
theorem raw_whisker_input (p : R) (F G : E ⥤ C) [F.Additive] [G.Additive]
    (hF : ScalarLocalization.IsSemilinear (RingHom.id R) F)
    (hG : ScalarLocalization.IsSemilinear (RingHom.id R) G)
    (U V : C × C ⥤ D) (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V)
    (hUF : IsSeparatelyLinear R (F.prod G ⋙ U))
    (hVF : IsSeparatelyLinear R (F.prod G ⋙ V)) (η : U ⟶ V) :
    ∃ (eU : (ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) F hF).prod
          (ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) G hG) ⋙ raw p U hU ≅
          raw p (F.prod G ⋙ U) hUF)
      (eV : (ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) F hF).prod
          (ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) G hG) ⋙ raw p V hV ≅
          raw p (F.prod G ⋙ V) hVF),
      (∀ X, HEq (eU.hom.app X) (𝟙 ((raw p (F.prod G ⋙ U) hUF).obj X)) ∧
        HEq (eV.hom.app X) (𝟙 ((raw p (F.prod G ⋙ V) hVF).obj X))) ∧
      Functor.whiskerLeft
          ((ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) F hF).prod
          (ScalarLocalization.extension p p (RingHom.id R)
            (IsLocalization.Away.algebraMap_isUnit p) G hG))
          (rawTransformation p U V hU hV η) ≫ eV.hom =
        eU.hom ≫ rawTransformation p (F.prod G ⋙ U) (F.prod G ⋙ V) hUF hVF
          (Functor.whiskerLeft (F.prod G) η) := by
  let eU := eqToIso (raw_input_eq p F G hF hG U hU hUF)
  let eV := eqToIso (raw_input_eq p F G hF hG V hV hVF)
  refine ⟨eU, eV, ?_, ?_⟩
  · intro X
    constructor <;> dsimp only [eU, eV, eqToIso] <;> rw [eqToHom_app] <;>
      exact eqToHom_heq_id_cod _ _ _
  · apply NatTrans.ext
    funext X
    apply eq_of_heq
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, eU, eV, eqToIso]
    rw [eqToHom_app, eqToHom_app]
    refine (comp_eqToHom_heq _ _).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    exact (rawTransformation_app p U V hU hV η _).trans
      (rawTransformation_app p (F.prod G ⋙ U) (F.prod G ⋙ V) hUF hVF
        (Functor.whiskerLeft (F.prod G) η) X).symm

/-- Addition, including signs in a supplied symmetry equation, survives raw rationalization.
Source: raw Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 13: tensor with one is an additive group homomorphism on every Hom module;
its additivity and preservation of negation give the component equations. -/
theorem raw_additive (p : R) (U V : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (hV : IsSeparatelyLinear R V) (η θ : U ⟶ V) :
    rawTransformation p U V hU hV (η + θ) =
      rawTransformation p U V hU hV η + rawTransformation p U V hU hV θ ∧
    rawTransformation p U V hU hV (-η) = -rawTransformation p U V hU hV η := by
  have hadd {X Y X' Y' : ScalarLocalization R D p}
      (hx : X = X') (hy : Y = Y') {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
      (hf : HEq f f') (hg : HEq g g') : HEq (f + g) (f' + g') := by
    subst X'; subst Y'
    exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hf) (eq_of_heq hg))
  have hneg {X Y X' Y' : ScalarLocalization R D p}
      (hx : X = X') (hy : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (hf : HEq f f') : HEq (-f) (-f') := by
    subst X'; subst Y'
    exact heq_of_eq (congrArg Neg.neg (eq_of_heq hf))
  constructor
  · apply NatTrans.ext
    funext X
    apply eq_of_heq
    refine (rawTransformation_app p U V hU hV (η + θ) X).trans ?_
    refine HEq.trans (heq_of_eq (TensorProduct.tmul_add _ _ _)) ?_
    exact (hadd (raw_obj p U hU X) (raw_obj p V hV X)
      (rawTransformation_app p U V hU hV η X)
      (rawTransformation_app p U V hU hV θ X)).symm
  · apply NatTrans.ext
    funext X
    apply eq_of_heq
    refine (rawTransformation_app p U V hU hV (-η) X).trans ?_
    refine HEq.trans (heq_of_eq (TensorProduct.tmul_neg _ _)) ?_
    exact (hneg (raw_obj p U hU X) (raw_obj p V hV X)
      (rawTransformation_app p U V hU hV η X)).symm

end RawWhiskering


attribute [local implicit_reducible] StageSystem.Morphism.functor StageSystem.ι

attribute [local implicit_reducible] rawNat

section CommonStage

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  {A₂ : I → Type u₂} [∀ i, Category.{v₂} (A₂ i)]
  {B : I → Type u'} [∀ i, Category.{v'} (B i)]
  (S : StageSystem A) (S₂ : StageSystem A₂) (T : StageSystem B)


/-- The family of identity comparisons, with its unchanged component type.
Source: supplied common-stage units
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitComparisons (S : StageSystem A) := ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)

/-- The two cocycles stored with specified identity comparisons.
Source: common-stage unit equations
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitLaws (S : StageSystem A) (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)) :
    Prop :=
  (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X)) ∧
    (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X))

/-- Specified identity comparisons and their two unit cocycles.
Source: common-stage formula, supplied identity and tower isomorphisms
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Units (S : StageSystem A) :=
  {unit : UnitComparisons S // UnitLaws S unit}

namespace Units

@[no_expose, implicit_reducible] def unit {S : StageSystem A} (uS : Units S) :
    ∀ i, S.T (le_refl i) ≅ 𝟭 (A i) := uS.val

omit [IsDirectedOrder I] in
theorem left {S : StageSystem A} (uS : Units S) {i j : I} (h : i ≤ j) (X : A i) :
    (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((uS.unit i).hom.app X) :=
  uS.property.1 h X

omit [IsDirectedOrder I] in
theorem right {S : StageSystem A} (uS : Units S) {i j : I} (h : i ≤ j) (X : A i) :
    (S.assoc h (le_refl j)).hom.app X = (uS.unit j).hom.app ((S.T h).obj X) :=
  uS.property.2 h X

@[no_expose] def mk {S : StageSystem A} (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i))
    (left : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X))
    (right : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)) :
    Units S := ⟨unit, left, right⟩


/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem unit_mk {S : StageSystem A} (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i))
    (left : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X))
    (right : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)) :
    (mk unit left right).unit = unit := by
  exact Eq.trans rfl rfl

end Units


/-- The tower law stored in a bilinear family.
Source: common-stage comparison cocycle
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def FamilyTower (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j) : Prop :=
  ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)

/-- A bilinear family with the specified scalar comparison and its tower equation.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Linearity is imposed separately at integral stages, not on this purely categorical interface. -/
structure Family where
  mkData ::
  functors : ∀ i, A i × A₂ i ⥤ B i
  comparisons : ∀ {i j : I} (h : i ≤ j),
    functors i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ functors j
  coherence : FamilyTower S S₂ T functors comparisons

namespace Family

variable {S S₂ T}

@[no_expose, implicit_reducible] def U (F : Family S S₂ T) : ∀ i, A i × A₂ i ⥤ B i := F.functors

@[no_expose, implicit_reducible] def comparison (F : Family S S₂ T) {i j : I} (h : i ≤ j) :
    F.U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ F.U j := F.comparisons h

omit [IsDirectedOrder I] in
theorem tower (F : Family S S₂ T) :
    ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((F.comparison h).hom.app (X, Y)) ≫
      (F.comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (F.U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((F.U i).obj (X, Y)) ≫
      (F.comparison (h.trans h')).hom.app (X, Y) :=
  F.coherence

@[no_expose] def mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)) : Family S S₂ T := Family.mkData U comparison tower


/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem U_mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)) :
    (mk U comparison tower).U = U := by
  exact Eq.trans rfl rfl

/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem comparison_mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y))
    {i j : I} (h : i ≤ j) :
    HEq ((mk U comparison tower).comparison h) (comparison h) := by
  exact HEq.trans HEq.rfl HEq.rfl

end Family

variable {S S₂ T}

/-- The identity cocycle for the supplied bilinear scalar comparison.
Source: common-stage formula, supplied λ identity cocycle
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
def HasUnitComparison (U : Family S S₂ T) (uS : Units S) (uS₂ : Units S₂)
    (uT : Units T) : Prop :=
  ∀ (i : I) (X : A i) (Y : A₂ i),
    (U.comparison (le_refl i)).hom.app (X, Y) ≫
      (U.U i).map (X := ((S.T (le_refl i)).obj X, (S₂.T (le_refl i)).obj Y))
        (Y := (X, Y)) ((uS.unit i).hom.app X, (uS₂.unit i).hom.app Y) =
        (uT.unit i).hom.app ((U.U i).obj (X, Y))

/-- The scalar square stored in a compatible transformation.
Source: common-stage transformation formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def TransformationSquare (U V : Family S S₂ T)
    (app : ∀ i, U.U i ⟶ V.U i) : Prop :=
  ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (app j).app ((S.T h).obj X, (S₂.T h).obj Y)

/-- Compatible transformations, including the scalar square of the statement.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure Transformation (U V : Family S S₂ T) where
  mkData ::
  components : ∀ i, U.U i ⟶ V.U i
  compatibility : TransformationSquare U V components

namespace Transformation

variable {U V : Family S S₂ T}

@[no_expose, implicit_reducible] def app (η : Transformation U V) (i : I) :
    U.U i ⟶ V.U i := η.components i

omit [IsDirectedOrder I] in
theorem square (η : Transformation U V) :
    ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((η.app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (η.app j).app ((S.T h).obj X, (S₂.T h).obj Y) := η.compatibility

@[no_expose] def mk (app : ∀ i, U.U i ⟶ V.U i)
    (square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
        (U.comparison h).hom.app (X, Y) ≫
          (app j).app ((S.T h).obj X, (S₂.T h).obj Y)) : Transformation U V :=
  Transformation.mkData app square


/-- Constructor normalization. Source: the supplied record data
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem app_mk (app : ∀ i, U.U i ⟶ V.U i)
    (square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
        (U.comparison h).hom.app (X, Y) ≫
          (app j).app ((S.T h).obj X, (S₂.T h).obj Y)) :
    (mk app square).app = app := by
  exact Eq.trans rfl rfl

end Transformation

/-- The specified common-field output object. Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
def output (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) : T.PairCategory :=
  ⟨join X.1.stage X.2.stage,
    (U.U _).obj (X.1.toStage (left _ _), X.2.toStage (right _ _))⟩

/-- The endpoint identification d from the node's proof, using both input associators.
Source: common-stage Hom formula, proof step 7
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
def endpoint (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) {L : I}
    (h : join X.1.stage X.2.stage ≤ L) :
    (T.T h).obj (output U join left right X).obj ≅
      (U.U L).obj (X.1.toStage ((left _ _).trans h),
        X.2.toStage ((right _ _).trans h)) :=
  (U.comparison h).app _ ≪≫ (U.U L).mapIso
    (Iso.prod ((S.assoc (left _ _) h).app X.1.obj)
      ((S₂.assoc (right _ _) h).app X.2.obj))

/-- The explicit object and common-stage arrow formulas, with equality of transported endpoints.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) : Prop where
  objects :
    ∀ X, F.obj X = output U join left right X
  arrows :
    ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
      (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
      (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
      (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
      HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
        StageSystem.PairCategory.mkHom L _ _ g))
        (StageSystem.PairCategory.mkHom (X := output U join left right X)
          (Y := output U join left right Y) L hX hY
          ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
            (endpoint U join left right Y hY).inv))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isDescent_iff (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) :
    IsDescent U join left right F ↔
  (∀ X, F.obj X = output U join left right X) ∧
  ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
    HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
      StageSystem.PairCategory.mkHom L _ _ g))
      (StageSystem.PairCategory.mkHom (X := output U join left right X)
        (Y := output U join left right Y) L hX hY
        ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
          (endpoint U join left right Y hY).inv)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

@[no_expose] private def productSystem (S : StageSystem A) (S₂ : StageSystem A₂) :
    StageSystem (fun i ↦ A i × A₂ i) where
  T h := (S.T h).prod (S₂.T h)
  assoc h h' := NatIso.ofComponents
    (fun X ↦ Iso.prod ((S.assoc h h').app X.1) ((S₂.assoc h h').app X.2))
    (by
      intro X Y f
      exact Prod.ext ((S.assoc h h').hom.naturality f.1)
        ((S₂.assoc h h').hom.naturality f.2))
  cocycle h h' h'' X := Prod.ext (S.cocycle h h' h'' X.1) (S₂.cocycle h h' h'' X.2)

@[no_expose] private def familyMorphism (U : Family S S₂ T) : (productSystem S S₂).Morphism T where
  Φ := U.U
  β := U.comparison
  coh h h' X := U.tower h h' X.1 X.2

@[no_expose] private def projectionLeft (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).Morphism S where
  Φ i := Prod.fst (A i) (A₂ i)
  β _ := Iso.refl _
  coh h h' X := by
    change (S.T h').map (𝟙 _) ≫ 𝟙 _ ≫ (S.assoc h h').hom.app X.1 =
      (S.assoc h h').hom.app X.1 ≫ 𝟙 _
    simp

@[no_expose] private def projectionRight (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).Morphism S₂ where
  Φ i := Prod.snd (A i) (A₂ i)
  β _ := Iso.refl _
  coh h h' X := by
    change (S₂.T h').map (𝟙 _) ≫ 𝟙 _ ≫ (S₂.assoc h h').hom.app X.2 =
      (S₂.assoc h h').hom.app X.2 ≫ 𝟙 _
    simp

@[no_expose] private def diagonal (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).PairCategory ⥤ S.PairCategory × S₂.PairCategory where
  obj X := (⟨X.stage, X.obj.1⟩, ⟨X.stage, X.obj.2⟩)
  map f := ((projectionLeft S S₂).functor.prod' (projectionRight S S₂).functor).map f
  map_id X := ((projectionLeft S S₂).functor.prod'
    (projectionRight S S₂).functor).map_id X
  map_comp f g := ((projectionLeft S S₂).functor.prod'
    (projectionRight S S₂).functor).map_comp f g

attribute [local implicit_reducible] productSystem familyMorphism projectionLeft
  projectionRight diagonal

private theorem diagonal_map (S : StageSystem A) (S₂ : StageSystem A₂)
    {X Y : (productSystem S S₂).PairCategory} {n : I}
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (f : X.toStage hX ⟶ Y.toStage hY) :
    (diagonal S S₂).map (StageSystem.PairCategory.mkHom n hX hY f) =
      (StageSystem.PairCategory.mkHom
        (X := ⟨X.stage, X.obj.1⟩) (Y := ⟨Y.stage, Y.obj.1⟩) n hX hY f.1,
        StageSystem.PairCategory.mkHom
          (X := ⟨X.stage, X.obj.2⟩) (Y := ⟨Y.stage, Y.obj.2⟩) n hX hY f.2) := by
  change (StageSystem.PairCategory.mkHom (S := S)
      (X := ⟨X.stage, X.obj.1⟩) (Y := ⟨Y.stage, Y.obj.1⟩) n hX hY (𝟙 _ ≫ f.1 ≫ 𝟙 _),
    StageSystem.PairCategory.mkHom (S := S₂)
      (X := ⟨X.stage, X.obj.2⟩) (Y := ⟨Y.stage, Y.obj.2⟩) n hX hY (𝟙 _ ≫ f.2 ≫ 𝟙 _)) = _
  simp only [Category.id_comp, Category.comp_id]

private theorem diagonal_bijective (S : StageSystem A) (S₂ : StageSystem A₂)
    (X Y : (productSystem S S₂).PairCategory) :
    Function.Bijective ((diagonal S S₂).map (X := X) (Y := Y)) := by
  constructor
  · intro f g he
    induction f using StageSystem.PairCategory.hom_induction with
    | h n hX hY u =>
      induction g using StageSystem.PairCategory.hom_induction with
      | h m hX' hY' v =>
        rw [diagonal_map, diagonal_map] at he
        obtain ⟨p, hn, hm, hp⟩ :=
          (StageSystem.PairCategory.mkHom_eq_mkHom_iff' (S := S)
            (X := ⟨X.stage, X.obj.1⟩) (Y := ⟨Y.stage, Y.obj.1⟩) u.1 v.1).1
              (congrArg _root_.Prod.fst he)
        obtain ⟨q, hn', hm', hq⟩ :=
          (StageSystem.PairCategory.mkHom_eq_mkHom_iff' (S := S₂)
            (X := ⟨X.stage, X.obj.2⟩) (Y := ⟨Y.stage, Y.obj.2⟩) u.2 v.2).1
              (congrArg _root_.Prod.snd he)
        obtain ⟨r, hpr, hqr⟩ := exists_ge_ge p q
        apply (StageSystem.PairCategory.mkHom_eq_mkHom_iff' u v).2
        refine ⟨r, hn.trans hpr, hm.trans hpr, ?_⟩
        apply Prod.ext
        · change S.tr (hn.trans hpr) u.1 = S.tr (hm.trans hpr) v.1
          have hr := congrArg (S.tr hpr) hp
          simpa only [S.tr_tr] using hr
        · change S₂.tr (hn.trans hpr) u.2 = S₂.tr (hm.trans hpr) v.2
          have hr := congrArg (S₂.tr hqr) hq
          simpa only [S₂.tr_tr] using hr
  · rintro ⟨f, g⟩
    obtain ⟨n, hn, hX, hY, u, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq f X.stage
    obtain ⟨m, hm, hX', hY', v, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq g n
    refine ⟨StageSystem.PairCategory.mkHom m (hX.trans hm) (hY.trans hm)
      (S.tr hm u, v), ?_⟩
    rw [diagonal_map, StageSystem.PairCategory.mkHom_tr]

@[no_expose] private def diagonalFF (S : StageSystem A) (S₂ : StageSystem A₂) :
    (diagonal S S₂).FullyFaithful :=
  ((Functor.FullyFaithful.nonempty_iff_map_bijective _).2 (diagonal_bijective S S₂)).some

@[no_expose] private def pairedObject (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) : (productSystem S S₂).PairCategory :=
  ⟨join X.1.stage X.2.stage,
    (X.1.toStage (left _ _), X.2.toStage (right _ _))⟩

@[no_expose] private def pairedIso (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) :
    (diagonal S S₂).obj (pairedObject S S₂ join left right X) ≅ X :=
  Iso.prod (S.isoToStage X.1 (left _ _)).symm
    (S₂.isoToStage X.2 (right _ _)).symm

@[no_expose] private def pairing (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    S.PairCategory × S₂.PairCategory ⥤ (productSystem S S₂).PairCategory where
  obj := pairedObject S S₂ join left right
  map {X Y} f := (diagonalFF S S₂).preimage
    ((pairedIso S S₂ join left right X).hom ≫ f ≫
      (pairedIso S S₂ join left right Y).inv)
  map_id X := by
    apply (diagonalFF S S₂).map_injective
    rw [(diagonalFF S S₂).map_preimage]
    simp
  map_comp {X Y Z} f g := by
    apply (diagonalFF S S₂).map_injective
    rw [Functor.map_comp]
    simp only [(diagonalFF S S₂).map_preimage, Category.assoc, Iso.inv_hom_id_assoc]

attribute [local implicit_reducible] pairedObject pairedIso pairing output endpoint

private theorem isoToStage_hom_eq (X : S.PairCategory) {j k : I}
    (a : X.stage ≤ j) (b : j ≤ k) :
    (S.isoToStage X a).hom = StageSystem.PairCategory.mkHom
      (X := X) (Y := (S.ι j).obj (X.toStage a))
      k (a.trans b) b ((S.assoc a b).inv.app X.obj) := by
  change StageSystem.PairCategory.mkHom j a (le_refl j) _ = _
  rw [← StageSystem.PairCategory.mkHom_tr b]
  apply congrArg (StageSystem.PairCategory.mkHom
    (X := X) (Y := (S.ι j).obj (X.toStage a)) k (a.trans b) b)
  dsimp only [StageSystem.tr]
  rw [← Category.assoc, S.cocycle_inv a (le_refl j) b, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem isoToStage_inv_eq (X : S.PairCategory) {j k : I}
    (a : X.stage ≤ j) (b : j ≤ k) :
    (S.isoToStage X a).inv = StageSystem.PairCategory.mkHom
      (X := (S.ι j).obj (X.toStage a)) (Y := X)
      k b (a.trans b) ((S.assoc a b).hom.app X.obj) := by
  apply (cancel_epi (S.isoToStage X a).hom).1
  rw [Iso.hom_inv_id, isoToStage_hom_eq X a b,
    StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.id_eq_mkHom X (a.trans b)]
  simp

private theorem conjugate_mkHom {X Y : S.PairCategory} {j j' k : I}
    (a : X.stage ≤ j) (a' : Y.stage ≤ j') (b : j ≤ k) (b' : j' ≤ k)
    (f : X.toStage (a.trans b) ⟶ Y.toStage (a'.trans b')) :
    (S.isoToStage X a).inv ≫ StageSystem.PairCategory.mkHom k _ _ f ≫
      (S.isoToStage Y a').hom =
    StageSystem.PairCategory.mkHom
      (X := (S.ι j).obj (X.toStage a)) (Y := (S.ι j').obj (Y.toStage a')) k b b'
      ((S.assoc a b).hom.app X.obj ≫ f ≫ (S.assoc a' b').inv.app Y.obj) := by
  rw [isoToStage_inv_eq X a b, isoToStage_hom_eq Y a' b',
    StageSystem.PairCategory.mkHom_comp_mkHom, StageSystem.PairCategory.mkHom_comp_mkHom]

private theorem pairing_map (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)) :
    (pairing S S₂ join left right).map
      (StageSystem.PairCategory.mkHom L _ _ f, StageSystem.PairCategory.mkHom L _ _ g) =
      StageSystem.PairCategory.mkHom L hX hY
        ((S.assoc (left _ _) hX).hom.app X.1.obj ≫ f ≫
            (S.assoc (left _ _) hY).inv.app Y.1.obj,
          (S₂.assoc (right _ _) hX).hom.app X.2.obj ≫ g ≫
            (S₂.assoc (right _ _) hY).inv.app Y.2.obj) := by
  apply (diagonalFF S S₂).map_injective
  rw [diagonal_map]
  change (diagonal S S₂).map ((diagonalFF S S₂).preimage _) = _
  rw [(diagonalFF S S₂).map_preimage]
  exact Prod.ext (conjugate_mkHom _ _ _ _ f) (conjugate_mkHom _ _ _ _ g)

private theorem exists_joint_representative
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X Y : S.PairCategory × S₂.PairCategory) (f : X.1 ⟶ Y.1) (g : X.2 ⟶ Y.2) :
    ∃ (L : I) (hX : join X.1.stage X.2.stage ≤ L)
      (hY : join Y.1.stage Y.2.stage ≤ L)
      (u : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
      (v : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
      f = StageSystem.PairCategory.mkHom L _ _ u ∧
        g = StageSystem.PairCategory.mkHom L _ _ v := by
  obtain ⟨m, hmX, hmY⟩ := exists_ge_ge (join X.1.stage X.2.stage) (join Y.1.stage Y.2.stage)
  obtain ⟨n, hmn, hX, hY, u, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq f m
  obtain ⟨L, hnL, hX', hY', v, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq g n
  exact ⟨L, hmX.trans (hmn.trans hnL), hmY.trans (hmn.trans hnL),
    S.tr hnL u, v, (StageSystem.PairCategory.mkHom_tr hnL u).symm, rfl⟩

@[no_expose] private def explicitDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    S.PairCategory × S₂.PairCategory ⥤ T.PairCategory where
  obj X := output U join left right X
  map f := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map f
  map_id X := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map_id X
  map_comp f g := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map_comp f g

private theorem explicitDescent_eq_core (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    explicitDescent U join left right =
      pairing S S₂ join left right ⋙ (familyMorphism U).functor := by
  rfl

private theorem explicitDescent_spec (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    IsDescent U join left right (explicitDescent U join left right) := by
  refine ⟨fun _ ↦ rfl, ?_⟩
  intro X Y L hX hY f g
  apply heq_of_eq
  dsimp only [explicitDescent, Functor.comp_map]
  rw [pairing_map S S₂ join left right X Y L hX hY f g,
    StageSystem.Morphism.functor_map_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom L hX hY)
  dsimp only [StageSystem.Morphism.mapAt, familyMorphism, endpoint, Iso.trans_hom,
    Iso.trans_inv, Iso.app, Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Iso.prod_hom, Iso.prod_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [prod_comp, Category.assoc]
  rfl

/-- Existence and uniqueness of the descended bifunctor with its explicit representatives.
Source: common-stage Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 5--9: choose a common upper stage for two arrow representatives and the output
fields. Conjugate U_L(f,g) by the endpoint identifications. The comparison tower equation,
the two input associator cocycles and comparison naturality show that this commutes with
transport. Equality of representatives is equality after a further common stage, so the
formula factors through the actual quotient Hom. Identity and composition follow by
cancelling adjacent endpoint isomorphisms. Every arrow has a representative, giving uniqueness.
This is the pair-category model of def-weil-algebraically-closed-coefficients, used without
any geometric, additive-object or triangulated hypotheses. -/
theorem descent_existsUnique (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    ∃! F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory,
      IsDescent U join left right F := by
  refine ⟨explicitDescent U join left right, explicitDescent_spec U join left right, ?_⟩
  intro F hF
  apply Functor.hext hF.1
  rintro X Y ⟨f, g⟩
  obtain ⟨L, hX, hY, u, v, rfl, rfl⟩ :=
    exists_joint_representative join left right X Y f g
  exact (hF.2 X Y L hX hY u v).trans
    ((explicitDescent_spec U join left right).2 X Y L hX hY u v).symm

/-- The unique representative-normalized descended bifunctor.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def descend (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :=
  withObjects (descent_existsUnique U join left right).exists.choose
    (output U join left right)
    (descent_existsUnique U join left right).exists.choose_spec.1

/-- The chosen common-stage functor satisfies the complete representative prescription.
Source: the proved unique descent
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem descend_spec (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    IsDescent U join left right (descend U join left right) := by
  unfold descend
  rw [withObjects_eq]
  exact (descent_existsUnique U join left right).exists.choose_spec

attribute [local implicit_reducible] explicitDescent

private theorem descend_eq (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    descend U join left right = explicitDescent U join left right :=
  (descent_existsUnique U join left right).unique
    (descend_spec U join left right)
    (explicitDescent_spec U join left right)

@[no_expose] private def familyHom (U V : Family S S₂ T) (η : Transformation U V) :
    StageSystem.Morphism.Hom (familyMorphism U) (familyMorphism V) where
  τ := η.app
  comm h X := η.square h X.1 X.2

/-- Descent of compatible transformations with the specified conjugate at every common stage.
Source: common-stage Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 10--11: the scalar square identifies the conjugate with S^D_{L/K}(η_K).
Transport therefore gives the same class at every L. With the input associators, naturality
identifies this with d_V inverse, η_L, d_U. The common-stage arrow formula and cancellation
of d prove naturality. The representatives specify every component, giving uniqueness. -/
theorem transformation_existsUnique (U V : Family S S₂ T) (η : Transformation U V)
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    ∃! e : descend U join left right ⟶ descend V join left right,
      ∀ (X : S.PairCategory × S₂.PairCategory) (L : I)
        (h : join X.1.stage X.2.stage ≤ L),
        HEq (e.app X)
          (StageSystem.PairCategory.mkHom (X := output U join left right X)
            (Y := output V join left right X) L h h
            ((U.comparison h).hom.app
                (X.1.toStage (left _ _), X.2.toStage (right _ _)) ≫
              (η.app L).app ((S.T h).obj (X.1.toStage (left _ _)),
                (S₂.T h).obj (X.2.toStage (right _ _))) ≫
              (V.comparison h).inv.app
                (X.1.toStage (left _ _), X.2.toStage (right _ _)))) := by
  let e := eqToHom (descend_eq U join left right) ≫
    Functor.whiskerLeft (pairing S S₂ join left right)
      (StageSystem.Morphism.descNatTrans (familyHom U V η)) ≫
        eqToHom (descend_eq V join left right).symm
  have hspec (X : S.PairCategory × S₂.PairCategory) (L : I)
      (h : join X.1.stage X.2.stage ≤ L) :
      HEq (e.app X)
        (StageSystem.PairCategory.mkHom (X := output U join left right X)
          (Y := output V join left right X) L h h
          ((U.comparison h).hom.app
            (X.1.toStage (left _ _), X.2.toStage (right _ _)) ≫
            (η.app L).app ((S.T h).obj (X.1.toStage (left _ _)),
              (S₂.T h).obj (X.2.toStage (right _ _))) ≫
            (V.comparison h).inv.app
              (X.1.toStage (left _ _), X.2.toStage (right _ _)))) := by
    have he : HEq (e.app X) ((T.ι (join X.1.stage X.2.stage)).map
        ((η.app _).app (X.1.toStage (left _ _), X.2.toStage (right _ _)))) := by
      dsimp only [e, NatTrans.comp_app]
      rw [eqToHom_app, eqToHom_app]
      exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
    refine he.trans (heq_of_eq ?_)
    rw [StageSystem.ι_map_eq h]
    apply congrArg (StageSystem.PairCategory.mkHom L h h)
    rw [← Category.assoc, ← η.square, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  refine ⟨e, hspec, ?_⟩
  intro θ hθ
  apply NatTrans.ext
  funext X
  exact eq_of_heq ((hθ X _ (le_refl _)).trans (hspec X _ (le_refl _)).symm)

/-- The uniquely specified transformation on the pair categories. Source: common-stage formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def descendTransformation (U V : Family S S₂ T) (η : Transformation U V)
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :=
  (transformation_existsUnique U V η join left right).exists.choose

/-- The chosen common-stage functor has its prescribed output.
Source: the uniquely prescribed construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem descend_obj (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) :
    (descend U join left right).obj X = output U join left right X := by
  exact Eq.trans rfl rfl

/-- The chosen transformation has its initial common-stage representative.
Source: the uniquely prescribed construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem descendTransformation_app (U V : Family S S₂ T) (η : Transformation U V)
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) :
    HEq ((descendTransformation U V η join left right).app X)
      ((T.ι (join X.1.stage X.2.stage)).map
        ((η.app _).app (X.1.toStage (left _ _), X.2.toStage (right _ _)))) := by
  have he := (transformation_existsUnique U V η join left right).exists.choose_spec
    X (join X.1.stage X.2.stage) (le_refl _)
  refine he.trans (heq_of_eq ?_)
  change StageSystem.PairCategory.mkHom _ _ _ _ = StageSystem.PairCategory.mkHom _ _ _ _
  congr 1
  dsimp only [output, StageSystem.PairCategory.toStage] at *
  rw [← Category.assoc, ← η.square, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

attribute [local irreducible] descend descendTransformation

/-- Identity, vertical composition, and inverses survive common-stage descent.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 10--12: represent every component as d_out inverse, η_L, d_in. Identity
components cancel d with its inverse. Vertical composition cancels the middle pair of d's.
For inverse families the same cancellation gives the inverse identities at a common stage.
Uniqueness of the specified components identifies the resulting transformations. -/
theorem descent_equations (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    (∀ (U : Family S S₂ T) (η : Transformation U U),
      (∀ i, η.app i = 𝟙 (U.U i)) →
        descendTransformation U U η join left right = 𝟙 _) ∧
    (∀ (U V W : Family S S₂ T) (η : Transformation U V) (θ : Transformation V W)
        (χ : Transformation U W), (∀ i, χ.app i = η.app i ≫ θ.app i) →
      descendTransformation U W χ join left right =
        descendTransformation U V η join left right ≫
          descendTransformation V W θ join left right) ∧
    (∀ (U V : Family S S₂ T) (η : Transformation U V),
      (∀ i, IsIso (η.app i)) → IsIso (descendTransformation U V η join left right)) := by
  constructor
  · intro U η hη
    apply NatTrans.ext
    funext X
    apply eq_of_heq
    have he := descendTransformation_app U U η join left right X
    rw [hη] at he
    simp only [NatTrans.id_app, Functor.map_id] at he
    exact he.trans (id_heq (descend_obj U join left right X)).symm
  constructor
  · intro U V W η θ χ hχ
    apply NatTrans.ext
    funext X
    apply eq_of_heq
    have he := descendTransformation_app U W χ join left right X
    rw [hχ] at he
    simp only [NatTrans.comp_app, Functor.map_comp] at he
    exact he.trans (heq_comp
      (descend_obj U join left right X) (descend_obj V join left right X)
      (descend_obj W join left right X)
      (descendTransformation_app U V η join left right X)
      (descendTransformation_app V W θ join left right X)).symm
  · intro U V η hη
    have := hη
    have : ∀ X, IsIso ((descendTransformation U V η join left right).app X) := by
      intro X
      have he := descendTransformation_app U V η join left right X
      have he' := (conj_eqToHom_iff_heq' _ _
        (descend_obj U join left right X) (descend_obj V join left right X).symm).2 he
      rw [he']
      let := hη (join X.1.stage X.2.stage)
      have : IsIso ((η.app (join X.1.stage X.2.stage)).app
        (X.1.toStage (left _ _), X.2.toStage (right _ _))) := by
        have := hη (join X.1.stage X.2.stage)
        infer_instance
      exact inferInstance
    exact NatIso.isIso_of_isIso_app _

@[no_expose] private def pairingComparison (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    pairing S S₂ j jl jr ≅ pairing S S₂ k kl kr :=
  NatIso.ofComponents
    (fun X ↦ (diagonalFF S S₂).preimageIso
      (pairedIso S S₂ j jl jr X ≪≫ (pairedIso S S₂ k kl kr X).symm)) (by
        intro X Y f
        apply (diagonalFF S S₂).map_injective
        simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
          (diagonalFF S S₂).map_preimage]
        change (diagonal S S₂).map ((diagonalFF S S₂).preimage _) ≫ _ =
          _ ≫ (diagonal S S₂).map ((diagonalFF S S₂).preimage _)
        simp only [(diagonalFF S S₂).map_preimage]
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Iso.inv_hom_id_assoc])

private theorem pairingComparison_app (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b)
    (X : S.PairCategory × S₂.PairCategory) (L : I)
    (h : j X.1.stage X.2.stage ≤ L) (h' : k X.1.stage X.2.stage ≤ L) :
    (pairingComparison j k jl jr kl kr).hom.app X =
      StageSystem.PairCategory.mkHom L h h'
        ((S.assoc (jl _ _) h).hom.app X.1.obj ≫ (S.assoc (kl _ _) h').inv.app X.1.obj,
          (S₂.assoc (jr _ _) h).hom.app X.2.obj ≫
            (S₂.assoc (kr _ _) h').inv.app X.2.obj) := by
  apply (diagonalFF S S₂).map_injective
  rw [diagonal_map]
  change (diagonal S S₂).map ((diagonalFF S S₂).preimage _) = _
  rw [(diagonalFF S S₂).map_preimage]
  apply Prod.ext
  · change (S.isoToStage X.1 (jl _ _)).inv ≫ (S.isoToStage X.1 (kl _ _)).hom = _
    rw [isoToStage_inv_eq _ _ h, isoToStage_hom_eq _ _ h',
      StageSystem.PairCategory.mkHom_comp_mkHom]
  · change (S₂.isoToStage X.2 (jr _ _)).inv ≫ (S₂.isoToStage X.2 (kr _ _)).hom = _
    rw [isoToStage_inv_eq _ _ h, isoToStage_hom_eq _ _ h',
      StageSystem.PairCategory.mkHom_comp_mkHom]

@[no_expose] private def descentComparison (U : Family S S₂ T) (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    descend U j jl jr ≅ descend U k kl kr :=
  eqToIso (descend_eq U j jl jr) ≪≫
    Functor.isoWhiskerRight (pairingComparison j k jl jr kl kr) (familyMorphism U).functor ≪≫
      (eqToIso (descend_eq U k kl kr)).symm

private theorem descentComparison_app (U : Family S S₂ T) (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b)
    (X : S.PairCategory × S₂.PairCategory) (L : I)
    (h : j X.1.stage X.2.stage ≤ L) (h' : k X.1.stage X.2.stage ≤ L) :
    HEq ((descentComparison U j k jl jr kl kr).hom.app X)
      (StageSystem.PairCategory.mkHom (X := output U j jl jr X)
        (Y := output U k kl kr X) L h h'
        ((endpoint U j jl jr X h).hom ≫ (endpoint U k kl kr X h').inv)) := by
  dsimp only [descentComparison, Iso.trans_hom, Iso.symm_hom, eqToIso,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [eqToHom_app, eqToHom_app]
  refine ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans ?_
  apply heq_of_eq
  rw [pairingComparison_app j k jl jr kl kr X L h h',
    StageSystem.Morphism.functor_map_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom L h h')
  simp only [StageSystem.Morphism.mapAt, familyMorphism, endpoint, Iso.trans_hom,
    Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Iso.prod_hom, Iso.prod_inv, Category.assoc]
  rw [← Functor.map_comp_assoc]
  rfl

/-- Changing the initial common field gives the canonical comparison with specified class.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 11: at a common upper L use d_1 followed by d_2 inverse. Transport compatibility
from step 8 makes its class independent of L. The arrow formulas prove naturality;
cancelling d's proves inverses and the cocycle. Conjugating a component cancels the same d's. -/
theorem change_common_field (U V : Family S S₂ T) (η : Transformation U V)
    (j k : I → I → I) (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    ∃ (cU : descend U j jl jr ≅ descend U k kl kr)
      (cV : descend V j jl jr ≅ descend V k kl kr),
      (∀ (X : S.PairCategory × S₂.PairCategory) (L : I)
        (h : j X.1.stage X.2.stage ≤ L) (h' : k X.1.stage X.2.stage ≤ L),
        HEq (cU.hom.app X)
          (StageSystem.PairCategory.mkHom (X := output U j jl jr X)
            (Y := output U k kl kr X) L h h'
            ((endpoint U j jl jr X h).hom ≫ (endpoint U k kl kr X h').inv)) ∧
        HEq (cV.hom.app X)
          (StageSystem.PairCategory.mkHom (X := output V j jl jr X)
            (Y := output V k kl kr X) L h h'
            ((endpoint V j jl jr X h).hom ≫ (endpoint V k kl kr X h').inv))) ∧
      descendTransformation U V η j jl jr ≫ cV.hom =
        cU.hom ≫ descendTransformation U V η k kl kr := by
  refine ⟨descentComparison U j k jl jr kl kr, descentComparison V j k jl jr kl kr,
    fun X L h h' ↦ ⟨descentComparison_app U j k jl jr kl kr X L h h',
      descentComparison_app V j k jl jr kl kr X L h h'⟩, ?_⟩
  apply NatTrans.ext
  funext X
  apply eq_of_heq
  have eU := descend_obj U j jl jr X
  have eV := descend_obj V j jl jr X
  dsimp only [NatTrans.comp_app, descentComparison, Iso.trans_hom, Iso.symm_hom,
    eqToIso, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [eqToHom_app, eqToHom_app, eqToHom_app, eqToHom_app]
  have hηj := descendTransformation_app U V η j jl jr X
  have hηk := descendTransformation_app U V η k kl kr X
  exact (heq_comp eU eV (descend_obj V k kl kr X) hηj
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))).trans
    ((heq_of_eq ((StageSystem.Morphism.descNatTrans (familyHom U V η)).naturality
      ((pairingComparison j k jl jr kl kr).hom.app X)).symm).trans
      (heq_comp eU (descend_obj U k kl kr X) (descend_obj V k kl kr X)
        ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)) hηk).symm)

/-- Any finite composite equation already identified at a common stage remains an equality.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 13: transport the finitely many representatives to a common upper stage, using
the finite compositum for coefficient fields. Both sides have the same outside endpoint
identifications. Equality there gives equality of the quotient classes. This applies after
any finite number of vertical compositions and whiskerings; supplied associativity, signed
symmetry, unit, pullback-composition and scalar-extension equations are instances. -/
theorem finite_equation_descent (X Y : T.PairCategory) (f g : X ⟶ Y)
    (L : I) (hX : X.stage ≤ L) (hY : Y.stage ≤ L)
    (u v : X.toStage hX ⟶ Y.toStage hY)
    (hf : f = StageSystem.PairCategory.mkHom L hX hY u)
    (hg : g = StageSystem.PairCategory.mkHom L hX hY v)
    (h : ∃ (M : I) (hLM : L ≤ M), (T.T hLM).map u = (T.T hLM).map v) : f = g := by
  rw [hf, hg]
  exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff u v).2 h

attribute [local irreducible] productSystem projectionLeft projectionRight diagonal diagonalFF
  pairedObject pairedIso pairing

private theorem morphism_hext
    {J : Type w} [Preorder J] {C₀ : J → Type u} [∀ i, Category.{v} (C₀ i)]
    {D₀ : J → Type u'} [∀ i, Category.{v'} (D₀ i)]
    {S₀ : StageSystem C₀} {T₀ : StageSystem D₀}
    (F G : S₀.Morphism T₀) (hΦ : ∀ i, F.Φ i = G.Φ i)
    (hβ : ∀ {i j : J} (h : i ≤ j) (X : C₀ i),
      HEq ((F.β h).hom.app X) ((G.β h).hom.app X)) : F = G := by
  rcases F with ⟨FΦ, Fβ, Fc⟩
  rcases G with ⟨GΦ, Gβ, Gc⟩
  have eΦ : FΦ = GΦ := funext hΦ
  cases eΦ
  have eβ : @Fβ = @Gβ := by
    funext i j h
    apply Iso.ext
    apply NatTrans.ext
    funext X
    exact eq_of_heq (hβ h X)
  cases eβ
  rfl

omit [IsDirectedOrder I] in
private theorem output_morphism
    {B₂ : I → Type u₃} [∀ i, Category.{v₃} (B₂ i)] {T₂ : StageSystem B₂}
    (F : T.Morphism T₂) (U : Family S S₂ T) (FU : Family S S₂ T₂)
    (hU : ∀ i, FU.U i = U.U i ⋙ F.Φ i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      HEq ((FU.comparison h).hom.app (X, Y))
        ((F.β h).hom.app ((U.U i).obj (X, Y)) ≫
          (F.Φ j).map ((U.comparison h).hom.app (X, Y)))) :
    familyMorphism FU = (familyMorphism U).comp F := by
  apply morphism_hext
  · exact hU
  · intro i j h X
    with_unfolding_all
      exact (cU h X.1 X.2).trans (heq_of_eq
        (StageSystem.Morphism.comp_β_hom_app (familyMorphism U) F h X).symm)

private theorem output_eq
    {B₂ : I → Type u₃} [∀ i, Category.{v₃} (B₂ i)] {T₂ : StageSystem B₂}
    (F : T.Morphism T₂) (U : Family S S₂ T) (FU : Family S S₂ T₂)
    (hm : familyMorphism FU = (familyMorphism U).comp F)
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    descend U join left right ⋙ F.functor = descend FU join left right := by
  rw [descend_eq, descend_eq]
  rw [explicitDescent_eq_core, explicitDescent_eq_core]
  rw [hm]
  apply Functor.hext
  · intro X
    rfl
  · intro X Y f
    exact heq_of_eq
      (StageSystem.Morphism.functor_comp_map (familyMorphism U) F
        ((pairing S S₂ join left right).map f)).symm

/-- Scalar-compatible output whiskering, including its comparison normalization.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 12, output case: F_L(d_U) followed after μ is precisely d_FU. Naturality of μ
moves it across each transformation component. The outside factors are the same, hence
both sides have equal representatives. This also applies with the other argument fixed
in a separately linear outer bifunctor. -/
theorem whisker_output
    {B₂ : I → Type u₃} [∀ i, Category.{v₃} (B₂ i)] {T₂ : StageSystem B₂}
    (F : T.Morphism T₂) (U V : Family S S₂ T) (η : Transformation U V)
    (FU FV : Family S S₂ T₂) (Fη : Transformation FU FV)
    (hU : ∀ i, FU.U i = U.U i ⋙ F.Φ i)
    (hV : ∀ i, FV.U i = V.U i ⋙ F.Φ i)
    (hη : ∀ i (X : A i) (Y : A₂ i),
      HEq ((Fη.app i).app (X, Y)) ((F.Φ i).map ((η.app i).app (X, Y))))
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      HEq ((FU.comparison h).hom.app (X, Y))
        ((F.β h).hom.app ((U.U i).obj (X, Y)) ≫
          (F.Φ j).map ((U.comparison h).hom.app (X, Y))))
    (cV : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      HEq ((FV.comparison h).hom.app (X, Y))
        ((F.β h).hom.app ((V.U i).obj (X, Y)) ≫
          (F.Φ j).map ((V.comparison h).hom.app (X, Y))))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    ∃ (eU : descend U join left right ⋙ F.functor ≅ descend FU join left right)
      (eV : descend V join left right ⋙ F.functor ≅ descend FV join left right),
      (∀ X, HEq (eU.hom.app X) (𝟙 ((descend FU join left right).obj X)) ∧
        HEq (eV.hom.app X) (𝟙 ((descend FV join left right).obj X))) ∧
      Functor.whiskerRight (descendTransformation U V η join left right) F.functor ≫ eV.hom =
        eU.hom ≫ descendTransformation FU FV Fη join left right := by
  have hmU := output_morphism F U FU hU cU
  have hmV := output_morphism F V FV hV cV
  let eU := eqToIso (output_eq F U FU hmU join left right)
  let eV := eqToIso (output_eq F V FV hmV join left right)
  have heU (X) : HEq (eU.hom.app X) (𝟙 ((descend FU join left right).obj X)) := by
    dsimp only [eU, eqToIso]
    rw [eqToHom_app]
    exact eqToHom_heq_id_cod _ _ _
  have heV (X) : HEq (eV.hom.app X) (𝟙 ((descend FV join left right).obj X)) := by
    dsimp only [eV, eqToIso]
    rw [eqToHom_app]
    exact eqToHom_heq_id_cod _ _ _
  refine ⟨eU, eV, fun X ↦ ⟨heU X, heV X⟩, ?_⟩
  apply NatTrans.ext
  funext X
  apply eq_of_heq
  have hu : (descend U join left right ⋙ F.functor).obj X =
      (descend FU join left right).obj X := by
    rw [Functor.comp_obj, descend_obj, descend_obj]
    change StageSystem.PairCategory.mk _ ((F.Φ _).obj _) = StageSystem.PairCategory.mk _ _
    congr 1
    exact congrArg (fun H ↦ H.obj
      (X.1.toStage (left _ _), X.2.toStage (right _ _))) (hU _).symm
  have hv : (descend V join left right ⋙ F.functor).obj X =
      (descend FV join left right).obj X := by
    rw [Functor.comp_obj, descend_obj, descend_obj]
    change StageSystem.PairCategory.mk _ ((F.Φ _).obj _) = StageSystem.PairCategory.mk _ _
    congr 1
    exact congrArg (fun H ↦ H.obj
      (X.1.toStage (left _ _), X.2.toStage (right _ _))) (hV _).symm
  have hm : HEq (F.functor.map ((descendTransformation U V η join left right).app X))
      ((descendTransformation FU FV Fη join left right).app X) := by
    have ha := descendTransformation_app U V η join left right X
    have hb := descendTransformation_app FU FV Fη join left right X
    have hmap : HEq (F.functor.map ((descendTransformation U V η join left right).app X))
        (F.functor.map ((T.ι _).map ((η.app _).app
          (X.1.toStage (left _ _), X.2.toStage (right _ _))))) := by
      exact map_heq F.functor (descend_obj U join left right X)
        (descend_obj V join left right X) ha
    refine hmap.trans ?_
    rw [StageSystem.Morphism.functor_map_ι]
    exact (map_heq (T₂.ι _) (by
      exact congrArg (fun H ↦ H.obj
        (X.1.toStage (left _ _), X.2.toStage (right _ _))) (hU _).symm) (by
      exact congrArg (fun H ↦ H.obj
        (X.1.toStage (left _ _), X.2.toStage (right _ _))) (hV _).symm)
      (hη _ _ _).symm).trans hb.symm
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app]
  exact (heq_comp hu hv rfl hm (heV X)).trans
    ((heq_of_eq (Category.comp_id _)).trans
      ((heq_of_eq (Category.id_comp _)).symm.trans
        (heq_comp hu rfl rfl (heU X) HEq.rfl).symm))

private theorem descendTransformation_endpoint (U V : Family S S₂ T)
    (η : Transformation U V) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) (L : I)
    (h : join X.1.stage X.2.stage ≤ L) :
    HEq ((descendTransformation U V η join left right).app X)
      (StageSystem.PairCategory.mkHom (X := output U join left right X)
        (Y := output V join left right X) L h h
        ((endpoint U join left right X h).hom ≫
          (η.app L).app (X.1.toStage ((left _ _).trans h),
            X.2.toStage ((right _ _).trans h)) ≫
          (endpoint V join left right X h).inv)) := by
  unfold descendTransformation
  refine ((transformation_existsUnique U V η join left right).exists.choose_spec X L h).trans ?_
  apply heq_of_eq
  apply congrArg (StageSystem.PairCategory.mkHom L h h)
  dsimp only [endpoint, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp]
  rfl

private theorem explicitDescent_map (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)) :
    (explicitDescent U join left right).map
      (StageSystem.PairCategory.mkHom L _ _ f, StageSystem.PairCategory.mkHom L _ _ g) =
    StageSystem.PairCategory.mkHom (X := output U join left right X)
      (Y := output U join left right Y) L hX hY
      ((endpoint U join left right X hX).hom ≫ (U.U L).map (f,g) ≫
        (endpoint U join left right Y hY).inv) :=
  eq_of_heq ((explicitDescent_spec U join left right).2 X Y L hX hY f g)

section InputLeft

variable
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S) (U : Family S S₂ T) (UF : Family S₀ S₂ T)
    (hU : ∀ i, UF.U i = ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A₀ i) (Y : A₂ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app ((F.Φ i).obj X, Y) ≫
          (U.U j).map (X := ((S.T h).obj ((F.Φ i).obj X), (S₂.T h).obj Y))
            (Y := ((F.Φ j).obj ((S₀.T h).obj X), (S₂.T h).obj Y))
            ((F.β h).hom.app X, 𝟙 _)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

include cU in
private theorem input_endpoint_left
    (X : S₀.PairCategory × S₂.PairCategory) {L : I}
    (h : join X.1.stage X.2.stage ≤ L) :
    HEq ((T.T h).map ((U.U (join X.1.stage X.2.stage)).map
        (X := ((S.T (left _ _)).obj ((F.Φ X.1.stage).obj X.1.obj),
          X.2.toStage (right _ _)))
        (Y := ((F.Φ (join X.1.stage X.2.stage)).obj (X.1.toStage (left _ _)),
          X.2.toStage (right _ _)))
        ((F.β (left _ _)).hom.app X.1.obj, 𝟙 _)))
      ((endpoint U join left right (F.functor.obj X.1, X.2) h).hom ≫
        (U.U L).map
          (X := ((S.T ((left _ _).trans h)).obj ((F.Φ X.1.stage).obj X.1.obj),
            X.2.toStage ((right _ _).trans h)))
          (Y := ((F.Φ L).obj (X.1.toStage ((left _ _).trans h)),
            X.2.toStage ((right _ _).trans h)))
          ((F.β ((left _ _).trans h)).hom.app X.1.obj, 𝟙 _) ≫
        eqToHom (congrArg (fun G : A₀ L × A₂ L ⥤ B L ↦
          G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
            X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hU L)).symm ≫
        (endpoint UF join left right X h).inv) := by
  rcases UF with ⟨UF, fc, ft⟩
  have hf : UF = fun i ↦ ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i := funext hU
  cases hf
  apply heq_of_eq
  simp only [eqToHom_refl]
  with_unfolding_all rw [← cancel_mono (endpoint ⟨_, fc, ft⟩ join left right X h).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [endpoint, Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.app_hom]
  erw [eq_of_heq (cU h _ _)]
  simp only [Category.assoc]
  have hn := (U.comparison h).hom.naturality
    (X := ((S.T (left X.1.stage X.2.stage)).obj ((F.Φ X.1.stage).obj X.1.obj),
      X.2.toStage (right X.1.stage X.2.stage)))
    (Y := ((F.Φ (join X.1.stage X.2.stage)).obj
        (X.1.toStage (left X.1.stage X.2.stage)),
      X.2.toStage (right X.1.stage X.2.stage)))
    ((F.β (left X.1.stage X.2.stage)).hom.app X.1.obj, 𝟙 _)
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  have hc := F.coh (left X.1.stage X.2.stage) h X.1.obj
  have hp :
      Prod.mkHom ((S.T h).map ((F.β (left _ _)).hom.app X.1.obj)) (𝟙 _) ≫
        Prod.mkHom ((F.β h).hom.app (X.1.toStage (left _ _))) (𝟙 _) ≫
          Prod.mkHom ((F.Φ L).map ((S₀.assoc (left _ _) h).hom.app X.1.obj))
            ((S₂.assoc (right _ _) h).hom.app X.2.obj) =
      Prod.mkHom ((S.assoc (left _ _) h).hom.app ((F.Φ X.1.stage).obj X.1.obj))
          ((S₂.assoc (right _ _) h).hom.app X.2.obj) ≫
        Prod.mkHom ((F.β ((left _ _).trans h)).hom.app X.1.obj) (𝟙 _) := by
    apply Prod.ext
    · exact hc
    · simp
  dsimp only [Family.U, Sigma.fst] at *
  simp only [Functor.comp_map, Functor.prod_map, Functor.map_id]
  apply congrArg ((U.comparison h).hom.app
    ((S.T (left _ _)).obj ((F.Φ X.1.stage).obj X.1.obj), X.2.toStage (right _ _)) ≫ ·)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (U.U L).map
  exact hp

@[no_expose] private def inputComponentLeft
    (X : S₀.PairCategory × S₂.PairCategory) :
    output U join left right (F.functor.obj X.1, X.2) ≅ output UF join left right X :=
  let K := join X.1.stage X.2.stage
  let Z := (X.1.toStage (left X.1.stage X.2.stage),
    X.2.toStage (right X.1.stage X.2.stage))
  (T.ι K).mapIso ((U.U K).mapIso
    (Iso.prod ((F.β (left X.1.stage X.2.stage)).app X.1.obj) (Iso.refl Z.2))) ≪≫
    eqToIso (congrArg (fun H : A₀ K × A₂ K ⥤ B K ↦
      (T.ι K).obj (H.obj Z)) (hU K)).symm

include cU in
private theorem inputComponentLeft_spec
    (X : S₀.PairCategory × S₂.PairCategory) {L : I}
    (h : join X.1.stage X.2.stage ≤ L) :
    (inputComponentLeft F U UF hU join left right X).hom =
      StageSystem.PairCategory.mkHom
        (X := output U join left right (F.functor.obj X.1, X.2))
        (Y := output UF join left right X) L h h
        ((endpoint U join left right (F.functor.obj X.1, X.2) h).hom ≫
          (U.U L).map
            (X := ((S.T ((left _ _).trans h)).obj ((F.Φ X.1.stage).obj X.1.obj),
              X.2.toStage ((right _ _).trans h)))
            (Y := ((F.Φ L).obj (X.1.toStage ((left _ _).trans h)),
              X.2.toStage ((right _ _).trans h)))
            ((F.β ((left _ _).trans h)).hom.app X.1.obj, 𝟙 _) ≫
          eqToHom (congrArg (fun G : A₀ L × A₂ L ⥤ B L ↦
            G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
              X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hU L)).symm ≫
          (endpoint UF join left right X h).inv) := by
  rcases UF with ⟨UF, fc, ft⟩
  have hf : UF = fun i ↦ ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i := funext hU
  cases hf
  dsimp only [inputComponentLeft, Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
    Iso.app_hom, Iso.refl_hom, eqToIso.hom, eqToHom_refl]
  simp only [Category.comp_id]
  rw [StageSystem.ι_map_eq h]
  apply congrArg (StageSystem.PairCategory.mkHom L h h)
  exact eq_of_heq (input_endpoint_left F U ⟨_,fc,ft⟩ hU cU join left right X h)

@[no_expose] private def inputIsoLeft :
    F.functor.prod (𝟭 S₂.PairCategory) ⋙ explicitDescent U join left right ≅
      explicitDescent UF join left right := by
  refine NatIso.ofComponents (inputComponentLeft F U UF hU join left right) ?_
  rcases UF with ⟨UF, fc, ft⟩
  have hf : UF = fun i ↦ ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i := funext hU
  cases hf
  let W : Family S₀ S₂ T := ⟨fun i ↦ ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i, fc, ft⟩
  intro X Y f
  obtain ⟨L, hX, hY, u, v, hf, hg⟩ :=
    exists_joint_representative join left right X Y f.1 f.2
  change (explicitDescent U join left right).map
      (X := (F.functor.obj X.1, X.2)) (Y := (F.functor.obj Y.1, Y.2))
      (F.functor.map f.1, f.2) ≫ _ =
    _ ≫ (explicitDescent W join left right).map f
  rcases f with ⟨f,g⟩
  dsimp only at hf hg
  subst f
  subst g
  rw [StageSystem.Morphism.functor_map_mkHom,
    explicitDescent_map U join left right _ _ L hX hY,
    explicitDescent_map W join left right X Y L hX hY,
    inputComponentLeft_spec F U W hU cU join left right X hX,
    inputComponentLeft_spec F U W hU cU join left right Y hY]
  dsimp only [output, StageSystem.ι]
  rw [StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom L hX hY)
  dsimp only [W, Family.U, Functor.comp_map, Functor.prod_map,
    Functor.id_map]
  simp only [eqToHom_refl, Category.assoc, Category.id_comp,
    Iso.inv_hom_id_assoc]
  have hp :
      Prod.mkHom (F.mapAt (hi := (left _ _).trans hX)
        (hj := (left _ _).trans hY) u) v ≫
          Prod.mkHom ((F.β ((left _ _).trans hY)).hom.app Y.1.obj) (𝟙 _) =
      Prod.mkHom ((F.β ((left _ _).trans hX)).hom.app X.1.obj) (𝟙 _) ≫
          Prod.mkHom ((F.Φ L).map u) v := by
    ext <;> simp [StageSystem.Morphism.mapAt]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hp]

@[no_expose] private def inputDescendIsoLeft :
    F.functor.prod (𝟭 S₂.PairCategory) ⋙ descend U join left right ≅
      descend UF join left right :=
  Functor.isoWhiskerLeft (F.functor.prod (𝟭 S₂.PairCategory))
      (eqToIso (descend_eq U join left right)) ≪≫
    inputIsoLeft F U UF hU cU join left right ≪≫
      eqToIso (descend_eq UF join left right).symm

private theorem inputDescendIsoLeft_app
    (X : S₀.PairCategory × S₂.PairCategory) :
    HEq ((inputDescendIsoLeft F U UF hU cU join left right).hom.app X)
      ((inputComponentLeft F U UF hU join left right X).hom) := by
  simp only [inputDescendIsoLeft, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
  apply (eqToHom_comp_heq_iff ..).2
  apply (comp_eqToHom_heq_iff ..).2
  rfl

end InputLeft

/-- Scalar-compatible input whiskering in the first slot, with its necessary object comparison.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 12, input case: the two output objects differ by μ in the indicated slot.
At L the comparison is d_UF inverse U_L(μ,1) d_U. The tower equation for μ together with
step 8 proves independence of L. Naturality follows from μ inverse F(f) μ. Conjugating
transformation components cancels the d's and applies stage naturality. The comparisons are
pinned to this class at every common stage L, the eqToHom only transporting the given
functor equation. -/
theorem whisker_input_left
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S) (U V : Family S S₂ T) (η : Transformation U V)
    (UF VF : Family S₀ S₂ T) (ηF : Transformation UF VF)
    (hU : ∀ i, UF.U i = ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i)
    (hV : ∀ i, VF.U i = ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ V.U i)
    (hη : ∀ i (X : A₀ i) (Y : A₂ i),
      HEq ((ηF.app i).app (X, Y)) ((η.app i).app ((F.Φ i).obj X, Y)))
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A₀ i) (Y : A₂ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app ((F.Φ i).obj X, Y) ≫
          (U.U j).map (X := ((S.T h).obj ((F.Φ i).obj X), (S₂.T h).obj Y))
            (Y := ((F.Φ j).obj ((S₀.T h).obj X), (S₂.T h).obj Y))
            ((F.β h).hom.app X, 𝟙 _)))
    (cV : ∀ {i j : I} (h : i ≤ j) (X : A₀ i) (Y : A₂ i),
      HEq ((VF.comparison h).hom.app (X, Y))
        ((V.comparison h).hom.app ((F.Φ i).obj X, Y) ≫
          (V.U j).map (X := ((S.T h).obj ((F.Φ i).obj X), (S₂.T h).obj Y))
            (Y := ((F.Φ j).obj ((S₀.T h).obj X), (S₂.T h).obj Y))
            ((F.β h).hom.app X, 𝟙 _)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    ∃ (eU : F.functor.prod (𝟭 S₂.PairCategory) ⋙ descend U join left right ≅
        descend UF join left right)
      (eV : F.functor.prod (𝟭 S₂.PairCategory) ⋙ descend V join left right ≅
        descend VF join left right),
      (∀ (X : S₀.PairCategory × S₂.PairCategory) (L : I)
        (h : join X.1.stage X.2.stage ≤ L),
        HEq (eU.hom.app X)
          (StageSystem.PairCategory.mkHom
            (X := output U join left right (F.functor.obj X.1, X.2))
            (Y := output UF join left right X) L h h
            ((endpoint U join left right (F.functor.obj X.1, X.2) h).hom ≫
              (U.U L).map
                (X := ((S.T ((left _ _).trans h)).obj ((F.Φ X.1.stage).obj X.1.obj),
                  X.2.toStage ((right _ _).trans h)))
                (Y := ((F.Φ L).obj (X.1.toStage ((left _ _).trans h)),
                  X.2.toStage ((right _ _).trans h)))
                ((F.β ((left _ _).trans h)).hom.app X.1.obj, 𝟙 _) ≫
              eqToHom (congrArg (fun G : A₀ L × A₂ L ⥤ B L ↦
                G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
                  X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hU L)).symm ≫
              (endpoint UF join left right X h).inv)) ∧
        HEq (eV.hom.app X)
          (StageSystem.PairCategory.mkHom
            (X := output V join left right (F.functor.obj X.1, X.2))
            (Y := output VF join left right X) L h h
            ((endpoint V join left right (F.functor.obj X.1, X.2) h).hom ≫
              (V.U L).map
                (X := ((S.T ((left _ _).trans h)).obj ((F.Φ X.1.stage).obj X.1.obj),
                  X.2.toStage ((right _ _).trans h)))
                (Y := ((F.Φ L).obj (X.1.toStage ((left _ _).trans h)),
                  X.2.toStage ((right _ _).trans h)))
                ((F.β ((left _ _).trans h)).hom.app X.1.obj, 𝟙 _) ≫
              eqToHom (congrArg (fun G : A₀ L × A₂ L ⥤ B L ↦
                G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
                  X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hV L)).symm ≫
              (endpoint VF join left right X h).inv))) ∧
      Functor.whiskerLeft (F.functor.prod (𝟭 S₂.PairCategory))
        (descendTransformation U V η join left right) ≫ eV.hom =
          eU.hom ≫ descendTransformation UF VF ηF join left right := by
  let eU := inputDescendIsoLeft F U UF hU cU join left right
  let eV := inputDescendIsoLeft F V VF hV cV join left right
  have hcU (X : S₀.PairCategory × S₂.PairCategory) :=
    inputDescendIsoLeft_app F U UF hU cU join left right X
  have hcV (X : S₀.PairCategory × S₂.PairCategory) :=
    inputDescendIsoLeft_app F V VF hV cV join left right X
  refine ⟨eU, eV, ?_, ?_⟩
  · intro X L h
    exact ⟨(hcU X).trans (heq_of_eq
      (inputComponentLeft_spec F U UF hU cU join left right X h)),
      (hcV X).trans (heq_of_eq
        (inputComponentLeft_spec F V VF hV cV join left right X h))⟩
  · apply NatTrans.ext
    funext X
    let L := join X.1.stage X.2.stage
    have h := le_refl L
    have hsU := inputComponentLeft_spec F U UF hU cU join left right X h
    have hsV := inputComponentLeft_spec F V VF hV cV join left right X h
    have he₁ := descendTransformation_endpoint U V η join left right
      (F.functor.obj X.1, X.2) L h
    have he₂ := descendTransformation_endpoint UF VF ηF join left right X L h
    have hl := heq_comp (descend_obj U join left right (F.functor.obj X.1, X.2))
      (descend_obj V join left right (F.functor.obj X.1, X.2))
      (descend_obj VF join left right X) he₁ ((hcV X).trans (heq_of_eq hsV))
    have hr := heq_comp (descend_obj U join left right (F.functor.obj X.1, X.2))
      (descend_obj UF join left right X) (descend_obj VF join left right X)
      ((hcU X).trans (heq_of_eq hsU)) he₂
    apply eq_of_heq (hl.trans ((heq_of_eq ?_).trans hr.symm))
    dsimp only [output] at *
    rw [StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom]
    apply congrArg (StageSystem.PairCategory.mkHom L h h)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rcases UF with ⟨UF, fc, ft⟩
    have hf : UF = fun i ↦ ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i := funext hU
    cases hf
    rcases VF with ⟨VF, gc, gt⟩
    have hf : VF = fun i ↦ ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ V.U i := funext hV
    cases hf
    simp only [eqToHom_refl, Category.id_comp]
    erw [eq_of_heq (hη L _ _)]
    have hn := (η.app L).naturality
      (X := ((S.T ((left _ _).trans h)).obj ((F.Φ X.1.stage).obj X.1.obj),
        X.2.toStage ((right _ _).trans h)))
      (Y := ((F.Φ L).obj (X.1.toStage ((left _ _).trans h)),
        X.2.toStage ((right _ _).trans h)))
      ((F.β ((left _ _).trans h)).hom.app X.1.obj, 𝟙 _)
    rw [reassoc_of% hn]
    rfl

section InputRight

variable
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S₂) (U : Family S S₂ T) (UF : Family S S₀ T)
    (hU : ∀ i, UF.U i = ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₀ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app (X, (F.Φ i).obj Y) ≫
          (U.U j).map (X := ((S.T h).obj X, (S₂.T h).obj ((F.Φ i).obj Y)))
            (Y := ((S.T h).obj X, (F.Φ j).obj ((S₀.T h).obj Y)))
            (𝟙 _, (F.β h).hom.app Y)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

include cU in
private theorem input_endpoint_right
    (X : S.PairCategory × S₀.PairCategory) {L : I}
    (h : join X.1.stage X.2.stage ≤ L) :
    HEq ((T.T h).map ((U.U (join X.1.stage X.2.stage)).map
        (X := (X.1.toStage (left _ _),
          (S₂.T (right _ _)).obj ((F.Φ X.2.stage).obj X.2.obj)))
        (Y := (X.1.toStage (left _ _),
          (F.Φ (join X.1.stage X.2.stage)).obj (X.2.toStage (right _ _))))
        (𝟙 _, (F.β (right _ _)).hom.app X.2.obj)))
      ((endpoint U join left right (X.1, F.functor.obj X.2) h).hom ≫
        (U.U L).map
          (X := (X.1.toStage ((left _ _).trans h),
            (S₂.T ((right _ _).trans h)).obj ((F.Φ X.2.stage).obj X.2.obj)))
          (Y := (X.1.toStage ((left _ _).trans h),
            (F.Φ L).obj (X.2.toStage ((right _ _).trans h))))
          (𝟙 _, (F.β ((right _ _).trans h)).hom.app X.2.obj) ≫
        eqToHom (congrArg (fun G : A L × A₀ L ⥤ B L ↦
          G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
            X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hU L)).symm ≫
        (endpoint UF join left right X h).inv) := by
  rcases UF with ⟨UF, fc, ft⟩
  have hf : UF = fun i ↦ ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i := funext hU
  cases hf
  apply heq_of_eq
  simp only [eqToHom_refl]
  with_unfolding_all rw [← cancel_mono (endpoint ⟨_, fc, ft⟩ join left right X h).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [endpoint, Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.app_hom]
  erw [eq_of_heq (cU h _ _)]
  simp only [Category.assoc]
  have hn := (U.comparison h).hom.naturality
    (X := (X.1.toStage (left X.1.stage X.2.stage),
      (S₂.T (right X.1.stage X.2.stage)).obj ((F.Φ X.2.stage).obj X.2.obj)))
    (Y := (X.1.toStage (left X.1.stage X.2.stage),
      (F.Φ (join X.1.stage X.2.stage)).obj
        (X.2.toStage (right X.1.stage X.2.stage))))
    (𝟙 _, (F.β (right X.1.stage X.2.stage)).hom.app X.2.obj)
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  have hc := F.coh (right X.1.stage X.2.stage) h X.2.obj
  have hp :
      Prod.mkHom (𝟙 _) ((S₂.T h).map ((F.β (right _ _)).hom.app X.2.obj)) ≫
        Prod.mkHom (𝟙 _) ((F.β h).hom.app (X.2.toStage (right _ _))) ≫
          Prod.mkHom ((S.assoc (left _ _) h).hom.app X.1.obj)
            ((F.Φ L).map ((S₀.assoc (right _ _) h).hom.app X.2.obj)) =
      Prod.mkHom ((S.assoc (left _ _) h).hom.app X.1.obj)
          ((S₂.assoc (right _ _) h).hom.app ((F.Φ X.2.stage).obj X.2.obj)) ≫
        Prod.mkHom (𝟙 _) ((F.β ((right _ _).trans h)).hom.app X.2.obj) := by
    apply Prod.ext
    · simp
    · exact hc
  dsimp only [Family.U, Sigma.fst] at *
  simp only [Functor.comp_map, Functor.prod_map, Functor.map_id]
  apply congrArg ((U.comparison h).hom.app
    (X.1.toStage (left _ _), (S₂.T (right _ _)).obj ((F.Φ X.2.stage).obj X.2.obj)) ≫ ·)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (U.U L).map
  exact hp

@[no_expose] private def inputComponentRight
    (X : S.PairCategory × S₀.PairCategory) :
    output U join left right (X.1, F.functor.obj X.2) ≅ output UF join left right X :=
  let K := join X.1.stage X.2.stage
  let Z := (X.1.toStage (left X.1.stage X.2.stage),
    X.2.toStage (right X.1.stage X.2.stage))
  (T.ι K).mapIso ((U.U K).mapIso
    (Iso.prod (Iso.refl Z.1) ((F.β (right X.1.stage X.2.stage)).app X.2.obj))) ≪≫
    eqToIso (congrArg (fun H : A K × A₀ K ⥤ B K ↦
      (T.ι K).obj (H.obj Z)) (hU K)).symm

include cU in
private theorem inputComponentRight_spec
    (X : S.PairCategory × S₀.PairCategory) {L : I}
    (h : join X.1.stage X.2.stage ≤ L) :
    (inputComponentRight F U UF hU join left right X).hom =
      StageSystem.PairCategory.mkHom
        (X := output U join left right (X.1, F.functor.obj X.2))
        (Y := output UF join left right X) L h h
        ((endpoint U join left right (X.1, F.functor.obj X.2) h).hom ≫
          (U.U L).map
            (X := (X.1.toStage ((left _ _).trans h),
              (S₂.T ((right _ _).trans h)).obj ((F.Φ X.2.stage).obj X.2.obj)))
            (Y := (X.1.toStage ((left _ _).trans h),
              (F.Φ L).obj (X.2.toStage ((right _ _).trans h))))
            (𝟙 _, (F.β ((right _ _).trans h)).hom.app X.2.obj) ≫
          eqToHom (congrArg (fun G : A L × A₀ L ⥤ B L ↦
            G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
              X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hU L)).symm ≫
          (endpoint UF join left right X h).inv) := by
  rcases UF with ⟨UF, fc, ft⟩
  have hf : UF = fun i ↦ ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i := funext hU
  cases hf
  dsimp only [inputComponentRight, Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
    Iso.app_hom, Iso.refl_hom, eqToIso.hom, eqToHom_refl]
  simp only [Category.comp_id]
  rw [StageSystem.ι_map_eq h]
  apply congrArg (StageSystem.PairCategory.mkHom L h h)
  exact eq_of_heq (input_endpoint_right F U ⟨_,fc,ft⟩ hU cU join left right X h)

@[no_expose] private def inputIsoRight :
    (𝟭 S.PairCategory).prod F.functor ⋙ explicitDescent U join left right ≅
      explicitDescent UF join left right := by
  refine NatIso.ofComponents (inputComponentRight F U UF hU join left right) ?_
  rcases UF with ⟨UF, fc, ft⟩
  have hf : UF = fun i ↦ ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i := funext hU
  cases hf
  let W : Family S S₀ T := ⟨fun i ↦ ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i, fc, ft⟩
  intro X Y f
  obtain ⟨L, hX, hY, u, v, hf, hg⟩ :=
    exists_joint_representative join left right X Y f.1 f.2
  change (explicitDescent U join left right).map
      (X := (X.1, F.functor.obj X.2)) (Y := (Y.1, F.functor.obj Y.2))
      (f.1, F.functor.map f.2) ≫ _ =
    _ ≫ (explicitDescent W join left right).map f
  rcases f with ⟨f,g⟩
  dsimp only at hf hg
  subst f
  subst g
  rw [StageSystem.Morphism.functor_map_mkHom,
    explicitDescent_map U join left right _ _ L hX hY,
    explicitDescent_map W join left right X Y L hX hY,
    inputComponentRight_spec F U W hU cU join left right X hX,
    inputComponentRight_spec F U W hU cU join left right Y hY]
  dsimp only [output, StageSystem.ι]
  rw [StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom L hX hY)
  dsimp only [W, Family.U, Functor.comp_map, Functor.prod_map,
    Functor.id_map]
  simp only [eqToHom_refl, Category.assoc, Category.id_comp,
    Iso.inv_hom_id_assoc]
  have hp :
      Prod.mkHom u (F.mapAt (hi := (right _ _).trans hX)
        (hj := (right _ _).trans hY) v) ≫
          Prod.mkHom (𝟙 _) ((F.β ((right _ _).trans hY)).hom.app Y.2.obj) =
      Prod.mkHom (𝟙 _) ((F.β ((right _ _).trans hX)).hom.app X.2.obj) ≫
          Prod.mkHom u ((F.Φ L).map v) := by
    ext <;> simp [StageSystem.Morphism.mapAt]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hp]

@[no_expose] private def inputDescendIsoRight :
    (𝟭 S.PairCategory).prod F.functor ⋙ descend U join left right ≅
      descend UF join left right :=
  Functor.isoWhiskerLeft ((𝟭 S.PairCategory).prod F.functor)
      (eqToIso (descend_eq U join left right)) ≪≫
    inputIsoRight F U UF hU cU join left right ≪≫
      eqToIso (descend_eq UF join left right).symm

private theorem inputDescendIsoRight_app
    (X : S.PairCategory × S₀.PairCategory) :
    HEq ((inputDescendIsoRight F U UF hU cU join left right).hom.app X)
      ((inputComponentRight F U UF hU join left right X).hom) := by
  simp only [inputDescendIsoRight, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
  apply (eqToHom_comp_heq_iff ..).2
  apply (comp_eqToHom_heq_iff ..).2
  rfl

end InputRight

/-- Scalar-compatible input whiskering in the second slot, with its necessary object comparison.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 12, input case: the two output objects differ by μ in the indicated slot.
At L the comparison is d_UF inverse U_L(μ,1) d_U. The tower equation for μ together with
step 8 proves independence of L. Naturality follows from μ inverse F(f) μ. Conjugating
transformation components cancels the d's and applies stage naturality. The comparisons are
pinned to this class at every common stage L, the eqToHom only transporting the given
functor equation. -/
theorem whisker_input_right
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S₂) (U V : Family S S₂ T) (η : Transformation U V)
    (UF VF : Family S S₀ T) (ηF : Transformation UF VF)
    (hU : ∀ i, UF.U i = ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i)
    (hV : ∀ i, VF.U i = ((𝟭 (A i)).prod (F.Φ i)) ⋙ V.U i)
    (hη : ∀ i (X : A i) (Y : A₀ i),
      HEq ((ηF.app i).app (X, Y)) ((η.app i).app (X, (F.Φ i).obj Y)))
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₀ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app (X, (F.Φ i).obj Y) ≫
          (U.U j).map (X := ((S.T h).obj X, (S₂.T h).obj ((F.Φ i).obj Y)))
            (Y := ((S.T h).obj X, (F.Φ j).obj ((S₀.T h).obj Y)))
            (𝟙 _, (F.β h).hom.app Y)))
    (cV : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₀ i),
      HEq ((VF.comparison h).hom.app (X, Y))
        ((V.comparison h).hom.app (X, (F.Φ i).obj Y) ≫
          (V.U j).map (X := ((S.T h).obj X, (S₂.T h).obj ((F.Φ i).obj Y)))
            (Y := ((S.T h).obj X, (F.Φ j).obj ((S₀.T h).obj Y)))
            (𝟙 _, (F.β h).hom.app Y)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    ∃ (eU : (𝟭 S.PairCategory).prod F.functor ⋙ descend U join left right ≅
        descend UF join left right)
      (eV : (𝟭 S.PairCategory).prod F.functor ⋙ descend V join left right ≅
        descend VF join left right),
      (∀ (X : S.PairCategory × S₀.PairCategory) (L : I)
        (h : join X.1.stage X.2.stage ≤ L),
        HEq (eU.hom.app X)
          (StageSystem.PairCategory.mkHom
            (X := output U join left right (X.1, F.functor.obj X.2))
            (Y := output UF join left right X) L h h
            ((endpoint U join left right (X.1, F.functor.obj X.2) h).hom ≫
              (U.U L).map
                (X := (X.1.toStage ((left _ _).trans h),
                  (S₂.T ((right _ _).trans h)).obj ((F.Φ X.2.stage).obj X.2.obj)))
                (Y := (X.1.toStage ((left _ _).trans h),
                  (F.Φ L).obj (X.2.toStage ((right _ _).trans h))))
                (𝟙 _, (F.β ((right _ _).trans h)).hom.app X.2.obj) ≫
              eqToHom (congrArg (fun G : A L × A₀ L ⥤ B L ↦
                G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
                  X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hU L)).symm ≫
              (endpoint UF join left right X h).inv)) ∧
        HEq (eV.hom.app X)
          (StageSystem.PairCategory.mkHom
            (X := output V join left right (X.1, F.functor.obj X.2))
            (Y := output VF join left right X) L h h
            ((endpoint V join left right (X.1, F.functor.obj X.2) h).hom ≫
              (V.U L).map
                (X := (X.1.toStage ((left _ _).trans h),
                  (S₂.T ((right _ _).trans h)).obj ((F.Φ X.2.stage).obj X.2.obj)))
                (Y := (X.1.toStage ((left _ _).trans h),
                  (F.Φ L).obj (X.2.toStage ((right _ _).trans h))))
                (𝟙 _, (F.β ((right _ _).trans h)).hom.app X.2.obj) ≫
              eqToHom (congrArg (fun G : A L × A₀ L ⥤ B L ↦
                G.obj (X.1.toStage ((left X.1.stage X.2.stage).trans h),
                  X.2.toStage ((right X.1.stage X.2.stage).trans h))) (hV L)).symm ≫
              (endpoint VF join left right X h).inv))) ∧
      Functor.whiskerLeft ((𝟭 S.PairCategory).prod F.functor)
        (descendTransformation U V η join left right) ≫ eV.hom =
          eU.hom ≫ descendTransformation UF VF ηF join left right := by
  let eU := inputDescendIsoRight F U UF hU cU join left right
  let eV := inputDescendIsoRight F V VF hV cV join left right
  have hcU (X : S.PairCategory × S₀.PairCategory) :=
    inputDescendIsoRight_app F U UF hU cU join left right X
  have hcV (X : S.PairCategory × S₀.PairCategory) :=
    inputDescendIsoRight_app F V VF hV cV join left right X
  refine ⟨eU, eV, ?_, ?_⟩
  · intro X L h
    exact ⟨(hcU X).trans (heq_of_eq
      (inputComponentRight_spec F U UF hU cU join left right X h)),
      (hcV X).trans (heq_of_eq
        (inputComponentRight_spec F V VF hV cV join left right X h))⟩
  · apply NatTrans.ext
    funext X
    let L := join X.1.stage X.2.stage
    have h := le_refl L
    have hsU := inputComponentRight_spec F U UF hU cU join left right X h
    have hsV := inputComponentRight_spec F V VF hV cV join left right X h
    have he₁ := descendTransformation_endpoint U V η join left right
      (X.1, F.functor.obj X.2) L h
    have he₂ := descendTransformation_endpoint UF VF ηF join left right X L h
    have hl := heq_comp (descend_obj U join left right (X.1, F.functor.obj X.2))
      (descend_obj V join left right (X.1, F.functor.obj X.2))
      (descend_obj VF join left right X) he₁ ((hcV X).trans (heq_of_eq hsV))
    have hr := heq_comp (descend_obj U join left right (X.1, F.functor.obj X.2))
      (descend_obj UF join left right X) (descend_obj VF join left right X)
      ((hcU X).trans (heq_of_eq hsU)) he₂
    apply eq_of_heq (hl.trans ((heq_of_eq ?_).trans hr.symm))
    dsimp only [output] at *
    rw [StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom]
    apply congrArg (StageSystem.PairCategory.mkHom L h h)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rcases UF with ⟨UF, fc, ft⟩
    have hf : UF = fun i ↦ ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i := funext hU
    cases hf
    rcases VF with ⟨VF, gc, gt⟩
    have hf : VF = fun i ↦ ((𝟭 (A i)).prod (F.Φ i)) ⋙ V.U i := funext hV
    cases hf
    simp only [eqToHom_refl, Category.id_comp]
    erw [eq_of_heq (hη L _ _)]
    have hn := (η.app L).naturality
      (X := (X.1.toStage ((left _ _).trans h),
        (S₂.T ((right _ _).trans h)).obj ((F.Φ X.2.stage).obj X.2.obj)))
      (Y := (X.1.toStage ((left _ _).trans h),
        (F.Φ L).obj (X.2.toStage ((right _ _).trans h))))
      (𝟙 _, (F.β ((right _ _).trans h)).hom.app X.2.obj)
    rw [reassoc_of% hn]
    rfl

end CommonStage


section RationalSystems

variable {I : Type w} [Preorder I]
  {O : I → Type r} [∀ i, CommRing (O i)] (π : ∀ i, O i)
  (φ : ∀ {i j : I}, i ≤ j → O i →+* O j)
  (unitImage : ∀ {i j : I} (h : i ≤ j),
    IsUnit (algebraMap (O j) (Localization.Away (π j)) (φ h (π i))))
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  [∀ i, Preadditive (A i)] [∀ i, Linear (O i) (A i)]
  (S : StageSystem A) [∀ (i j : I) (h : i ≤ j), (S.T h).Additive]
  (semi : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (S.T h))

/-- The exact transition and associator normalization of rationalization.
Source: raw Hom formula, proof step 4
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsRationalSystem
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))) : Prop where
  transitions :
    ∀ {i j : I} (h : i ≤ j), Q.T h =
      ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)
  associators :
    ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i),
      HEq ((Q.assoc h h').hom.app ⟨X⟩)
        ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').hom.app X) ∧
      HEq ((Q.assoc h h').inv.app ⟨X⟩)
        ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').inv.app X)

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isRationalSystem_iff
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))) :
    IsRationalSystem π φ unitImage S semi Q ↔
  (∀ {i j : I} (h : i ≤ j), Q.T h =
    ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)) ∧
  (∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i),
    HEq ((Q.assoc h h').hom.app ⟨X⟩)
      ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').hom.app X) ∧
    HEq ((Q.assoc h h').inv.app ⟨X⟩)
      ((1 : Localization.Away (π k)) ⊗ₜ[O k] (S.assoc h h').inv.app X)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

private theorem coefficientMap_comp {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (φcomp : (φ h').comp (φ h) = φ (h.trans h')) :
    (ScalarLocalization.coefficientMap (π j) (π k) (φ h') (unitImage h')).comp
      (ScalarLocalization.coefficientMap (π i) (π j) (φ h) (unitImage h)) =
      ScalarLocalization.coefficientMap (π i) (π k) (φ (h.trans h'))
        (unitImage (h.trans h')) := by
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
  ext r
  simp only [RingHom.comp_apply, ScalarLocalization.coefficientMap,
    IsLocalization.Away.lift_eq]
  exact congrArg (algebraMap (O k) (Localization.Away (π k))) (RingHom.congr_fun φcomp r)

private theorem rationalAssociator_naturality {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (φcomp : (φ h').comp (φ h) = φ (h.trans h')) (X Y : A i)
    (f : Localization.Away (π i) ⊗[O i] (X ⟶ Y)) :
    tensorComp (O k) (A k) (π k) _ _ _
        (1 ⊗ₜ[O k] (S.assoc h h').hom.app Y)
        (ScalarLocalization.extensionHom (π j) (π k) (φ h') (unitImage h')
          (S.T h') (semi h') ((S.T h).obj X) ((S.T h).obj Y)
          (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
            (S.T h) (semi h) X Y f)) =
      tensorComp (O k) (A k) (π k) _ _ _
        (ScalarLocalization.extensionHom (π i) (π k) (φ (h.trans h'))
          (unitImage (h.trans h')) (S.T (h.trans h')) (semi (h.trans h')) X Y f)
        (1 ⊗ₜ[O k] (S.assoc h h').hom.app X) := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [tensorComp_zero_left, tensorComp_zero_right,
    AddMonoidHom.map_zero]
  | add f g hf hg =>
    simp only [tensorComp_add_left, tensorComp_add_right, AddMonoidHom.map_add]
    exact congrArg₂ (· + ·) hf hg
  | tmul a f =>
    rw [extendedHom_tmul, extendedHom_tmul, extendedHom_tmul,
      tensorComp_tmul, tensorComp_tmul]
    simp only [one_mul, mul_one]
    have hc := RingHom.congr_fun (coefficientMap_comp π φ unitImage h h' φcomp) a
    simp only [RingHom.comp_apply] at hc
    rw [hc]
    exact congrArg (fun f ↦ ScalarLocalization.coefficientMap (π i) (π k)
      (φ (h.trans h')) (unitImage (h.trans h')) a ⊗ₜ[O k] f)
      ((S.assoc h h').hom.naturality f)

@[no_expose] private def rationalAssociator {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (φcomp : (φ h').comp (φ h) = φ (h.trans h')) :
    ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h) ⋙
      ScalarLocalization.extension (π j) (π k) (φ h') (unitImage h') (S.T h') (semi h') ≅
    ScalarLocalization.extension (π i) (π k) (φ (h.trans h')) (unitImage (h.trans h'))
      (S.T (h.trans h')) (semi (h.trans h')) :=
  NatIso.ofComponents
    (fun X ↦ (ScalarLocalization.localization (O k) (A k) (π k)).mapIso
      ((S.assoc h h').app X.obj)) (by
        intro X Y f
        exact rationalAssociator_naturality π φ unitImage S semi h h' φcomp X.obj Y.obj f)

@[no_expose] private def rationalSystem
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h')) :
    StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i)) where
  T h := ScalarLocalization.extension (π _) (π _) (φ h) (unitImage h) (S.T h) (semi h)
  assoc h h' := rationalAssociator π φ unitImage S semi h h' (φcomp h h')
  cocycle h h' h'' X := by
    with_unfolding_all
      change tensorComp (O _) (A _) (π _) _ _ _
          (1 ⊗ₜ[O _] (S.assoc (h.trans h') h'').hom.app X.obj)
          ((ScalarLocalization.extension (π _) (π _) (φ h'') (unitImage h'')
            (S.T h'') (semi h'')).map (1 ⊗ₜ[O _] (S.assoc h h').hom.app X.obj)) =
        tensorComp (O _) (A _) (π _) _ _ _
          (1 ⊗ₜ[O _] (S.assoc h (h'.trans h'')).hom.app X.obj)
          (1 ⊗ₜ[O _] (S.assoc h' h'').hom.app ((S.T h).obj X.obj))
      rw [extension_tmul, map_one, tensorComp_tmul,
        tensorComp_tmul, one_mul]
      exact congrArg (fun f ↦ (1 : Localization.Away (π _)) ⊗ₜ[O _] f)
        (S.cocycle h h' h'' X.obj)

private theorem rationalUnit_naturality
    (φid : ∀ i, φ (le_refl i) = RingHom.id (O i)) (uS : Units S)
    (i : I) (X Y : A i) (f : Localization.Away (π i) ⊗[O i] (X ⟶ Y)) :
    tensorComp (O i) (A i) (π i) _ _ _
        (1 ⊗ₜ[O i] (uS.unit i).hom.app Y)
        (ScalarLocalization.extensionHom (π i) (π i) (φ (le_refl i))
          (unitImage (le_refl i)) (S.T (le_refl i)) (semi (le_refl i)) X Y f) =
      tensorComp (O i) (A i) (π i) _ _ _ f
        (1 ⊗ₜ[O i] (uS.unit i).hom.app X) := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [tensorComp_zero_left, tensorComp_zero_right,
    AddMonoidHom.map_zero]
  | add f g hf hg =>
    simp only [tensorComp_add_left, tensorComp_add_right, AddMonoidHom.map_add]
    exact congrArg₂ (· + ·) hf hg
  | tmul a f =>
    rw [extendedHom_tmul]
    have hc : ScalarLocalization.coefficientMap (π i) (π i)
        (φ (le_refl i)) (unitImage (le_refl i)) = RingHom.id _ := by
      symm
      apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
      rw [φid]
      rfl
    rw [hc]
    simp only [RingHom.id_apply, tensorComp_tmul, one_mul, mul_one]
    exact congrArg (fun f ↦ a ⊗ₜ[O i] f) ((uS.unit i).hom.naturality f)

@[no_expose] private def rationalUnits
    (φid : ∀ i, φ (le_refl i) = RingHom.id (O i))
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h')) (uS : Units S) :
    Units (rationalSystem π φ unitImage S semi φcomp) := by
  refine ⟨(fun i ↦ NatIso.ofComponents
    (fun X ↦ (ScalarLocalization.localization (O i) (A i) (π i)).mapIso
      ((uS.unit i).app X.obj)) (by
        intro X Y f
        exact rationalUnit_naturality π φ unitImage S semi φid uS i X.obj Y.obj f)
  ), ?_, ?_⟩
  · intro i j h X
    change (1 : Localization.Away (π _)) ⊗ₜ[O _] (S.assoc (le_refl _) h).hom.app X.obj = _
    change (1 : Localization.Away (π _)) ⊗ₜ[O _] _ =
      (ScalarLocalization.extension (π _) (π _) (φ h) (unitImage h)
        (S.T h) (semi h)).map (1 ⊗ₜ[O _] (uS.unit _).hom.app X.obj)
    rw [extension_tmul, map_one]
    exact congrArg (fun f ↦ (1 : Localization.Away (π _)) ⊗ₜ[O _] f) (uS.left h X.obj)
  · intro i j h X
    exact congrArg (fun f ↦ (1 : Localization.Away (π _)) ⊗ₜ[O _] f) (uS.right h X.obj)

/-- Rationalizing coherent transitions, including non-strict identity transitions.
Source: raw Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 4: apply lem-pur-semilinear-scalar-localization to each transition. Tensor
associator components and inverses with one. Naturality follows on pure tensors by
semilinearity; tensor induction extends it. Tensor the cocycle equation with one.
All transitions and associator components are prescribed, so the system is unique. -/
theorem rational_system_existsUnique
    (φid : ∀ i, φ (le_refl i) = RingHom.id (O i))
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h')) :
    ∃! Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i)),
      IsRationalSystem π φ unitImage S semi Q := by
  have _ := φid
  refine ⟨rationalSystem π φ unitImage S semi φcomp, ?_, ?_⟩
  · exact ⟨fun _ ↦ rfl, fun _ _ _ ↦ ⟨HEq.rfl, HEq.rfl⟩⟩
  · intro Q hQ
    rcases Q with ⟨QT, Qa, Qc⟩
    have hT : @QT = @(rationalSystem π φ unitImage S semi φcomp).T := by
      funext i j h
      exact hQ.1 h
    cases hT
    have ha : @Qa = @(rationalSystem π φ unitImage S semi φcomp).assoc := by
      funext i j k h h'
      apply Iso.ext
      apply NatTrans.ext
      funext X
      exact eq_of_heq (hQ.2 h h' X.obj).1
    cases ha
    rfl

variable {π φ unitImage S semi}

/-- Exact normalization of a rationalized bilinear family.
Source: raw Hom formula, proof step 4
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsRationalFamily
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    {T : StageSystem B} (U : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))}
    {P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i))}
    (F : Family Q Q P) : Prop where
  functors :
    ∀ i, F.U i = raw (π i) (U.U i) (hU i)
  comparisons :
    ∀ {i j : I} (h : i ≤ j) (X Y : A i),
      HEq ((F.comparison h).hom.app (⟨X⟩, ⟨Y⟩))
        ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) ∧
      HEq ((F.comparison h).inv.app (⟨X⟩, ⟨Y⟩))
        ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).inv.app (X, Y))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isRationalFamily_iff
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    {T : StageSystem B} (U : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i))}
    {P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i))}
    (F : Family Q Q P) :
    IsRationalFamily U hU F ↔
  (∀ i, F.U i = raw (π i) (U.U i) (hU i)) ∧
  (∀ {i j : I} (h : i ≤ j) (X Y : A i),
    HEq ((F.comparison h).hom.app (⟨X⟩, ⟨Y⟩))
      ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) ∧
    HEq ((F.comparison h).inv.app (⟨X⟩, ⟨Y⟩))
      ((1 : Localization.Away (π j)) ⊗ₜ[O j] (U.comparison h).inv.app (X, Y))) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

private theorem rationalComparison_naturality
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (U : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {i j : I} (h : i ≤ j) (X X' Y Y' : A i)
    (f : Localization.Away (π i) ⊗[O i] (X ⟶ X'))
    (g : Localization.Away (π i) ⊗[O i] (Y ⟶ Y')) :
    tensorComp (O j) (B j) (π j) _ _ _
        (1 ⊗ₜ[O j] (U.comparison h).hom.app (X', Y'))
        (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
          (T.T h) (semiT h) ((U.U i).obj (X, Y)) ((U.U i).obj (X', Y'))
          (rawHom (π i) (U.U i) (hU i) X X' Y Y' f g)) =
      tensorComp (O j) (B j) (π j) _ _ _
        (rawHom (π j) (U.U j) (hU j)
          ((S.T h).obj X) ((S.T h).obj X') ((S.T h).obj Y) ((S.T h).obj Y')
          (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
            (S.T h) (semi h) X X' f)
          (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
            (S.T h) (semi h) Y Y' g))
        (1 ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [tensorComp_zero_left, tensorComp_zero_right, rawHom_zero_left,
    AddMonoidHom.map_zero]
  | add f f' hf hf' =>
    simp only [tensorComp_add_left, tensorComp_add_right, rawHom_add_left,
      AddMonoidHom.map_add]
    exact congrArg₂ (· + ·) hf hf'
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp only [tensorComp_zero_left, tensorComp_zero_right, rawHom_zero_right,
      AddMonoidHom.map_zero]
    | add g g' hg hg' =>
      simp only [tensorComp_add_left, tensorComp_add_right, rawHom_add_right,
        AddMonoidHom.map_add]
      exact congrArg₂ (· + ·) hg hg'
    | tmul b g =>
      rw [rawHom_tmul, extendedHom_tmul, extendedHom_tmul, extendedHom_tmul,
        rawHom_tmul, map_mul, tensorComp_tmul,
        tensorComp_tmul, one_mul, mul_one]
      exact congrArg (fun f ↦
        (ScalarLocalization.coefficientMap (π i) (π j) (φ h) (unitImage h) a *
          ScalarLocalization.coefficientMap (π i) (π j) (φ h) (unitImage h) b) ⊗ₜ[O j] f)
        ((U.comparison h).hom.naturality (X := (X,Y)) (Y := (X',Y')) (f,g))

@[no_expose] private def rationalComparisonIso
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (U : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {i j : I} (h : i ≤ j) :
    rawFunctor (π i) (U.U i) (hU i) ⋙
        ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (T.T h) (semiT h) ≅
      (ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)).prod
        (ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)) ⋙
        rawFunctor (π j) (U.U j) (hU j) :=
  NatIso.ofComponents
    (fun X ↦ (ScalarLocalization.localization (O j) (B j) (π j)).mapIso
      ((U.comparison h).app (X.1.obj, X.2.obj))) (by
        intro X Y f
        exact rationalComparison_naturality T semiT U hU h
          X.1.obj Y.1.obj X.2.obj Y.2.obj f.1 f.2)

private theorem rational_family
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i)))
    (P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i)))
    (hQ : IsRationalSystem π φ unitImage S semi Q)
    (hP : IsRationalSystem π φ unitImage T semiT P)
    (U : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i)) :
    ∃ F : Family Q Q P, IsRationalFamily U hU F := by
  rcases Q with ⟨QT, Qa, Qc⟩
  have eQ : @QT = fun i j h ↦ ScalarLocalization.extension (π i) (π j) (φ h)
      (unitImage h) (S.T h) (semi h) := by
    funext i j h
    exact hQ.1 h
  cases eQ
  rcases P with ⟨PT, Pa, Pc⟩
  have eP : @PT = fun i j h ↦ ScalarLocalization.extension (π i) (π j) (φ h)
      (unitImage h) (T.T h) (semiT h) := by
    funext i j h
    exact hP.1 h
  cases eP
  let F : Family ⟨_, Qa, Qc⟩ ⟨_, Qa, Qc⟩ ⟨_, Pa, Pc⟩ :=
    ⟨(fun i ↦ rawFunctor (π i) (U.U i) (hU i)),
      (fun h ↦ rationalComparisonIso T semiT U hU h), by
        intro i j k h h' X Y
        change (ScalarLocalization.extension (π j) (π k) (φ h') (unitImage h')
            (T.T h') (semiT h')).map
              (1 ⊗ₜ[O j] (U.comparison h).hom.app (X.obj, Y.obj)) ≫
            (1 ⊗ₜ[O k] (U.comparison h').hom.app
              ((S.T h).obj X.obj, (S.T h).obj Y.obj)) ≫
            rawHom (π k) (U.U k) (hU k) _ _ _ _
              ((Qa h h').hom.app X) ((Qa h h').hom.app Y) =
          (Pa h h').hom.app ⟨(U.U i).obj (X.obj, Y.obj)⟩ ≫
            (1 ⊗ₜ[O k] (U.comparison (h.trans h')).hom.app (X.obj, Y.obj))
        rw [eq_of_heq (hQ.2 h h' X.obj).1, eq_of_heq (hQ.2 h h' Y.obj).1,
          eq_of_heq (hP.2 h h' ((U.U i).obj (X.obj, Y.obj))).1]
        rw [← Category.assoc]
        change tensorComp (O k) (B k) (π k) _ _ _
            (rawHom (π k) (U.U k) (hU k) _ _ _ _
              (1 ⊗ₜ[O k] (S.assoc h h').hom.app X.obj)
              (1 ⊗ₜ[O k] (S.assoc h h').hom.app Y.obj))
            (tensorComp (O k) (B k) (π k) _ _ _
              (1 ⊗ₜ[O k] (U.comparison h').hom.app
                ((S.T h).obj X.obj, (S.T h).obj Y.obj))
              ((ScalarLocalization.extension (π j) (π k) (φ h') (unitImage h')
                (T.T h') (semiT h')).map
                (1 ⊗ₜ[O j] (U.comparison h).hom.app (X.obj, Y.obj)))) =
          tensorComp (O k) (B k) (π k) _ _ _
            (1 ⊗ₜ[O k] (U.comparison (h.trans h')).hom.app (X.obj, Y.obj))
            (1 ⊗ₜ[O k] (T.assoc h h').hom.app ((U.U i).obj (X.obj, Y.obj)))
        rw [extension_tmul, map_one, rawHom_tmul, one_mul,
          tensorComp_tmul, tensorComp_tmul,
          tensorComp_tmul]
        simp only [one_mul]
        exact congrArg (fun f ↦ (1 : Localization.Away (π k)) ⊗ₜ[O k] f)
          (by simpa only [Category.assoc] using U.tower h h' X.obj Y.obj)⟩
  exact ⟨F, fun i ↦ (raw_eq _ _ _).symm,
    fun _ _ _ ↦ ⟨HEq.rfl, HEq.rfl⟩⟩

/-- Rationalize bifunctors, comparisons, and their compatible natural isomorphism together.
Source: raw Hom and common-stage formulas
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 1--4: extend each bifunctor using raw_extension_existsUnique. Tensor λ and
its inverse with one. Naturality on pure tensors is the integral equation multiplied
by the image of ab; extend by tensor induction. Tensor tower and scalar-square equations
with one. Tensor η and its inverse with one as in step 3. Every component is prescribed.
In particular the resulting square is the original scalar square, not a chosen comparison. -/
theorem rational_comparison
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i)))
    (P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i)))
    (hQ : IsRationalSystem π φ unitImage S semi Q)
    (hP : IsRationalSystem π φ unitImage T semiT P)
    (U V : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    (hV : ∀ i, IsSeparatelyLinear (O i) (V.U i)) (η : Transformation U V)
    [hη : ∀ i, IsIso (η.app i)] :
    ∃ (F G : Family Q Q P) (e : Transformation F G),
      IsRationalFamily U hU F ∧ IsRationalFamily V hV G ∧
      (∃ he : ∀ i, IsIso (e.app i),
      (∀ (i : I) (X Y : A i),
        HEq ((e.app i).app (⟨X⟩, ⟨Y⟩))
          ((1 : Localization.Away (π i)) ⊗ₜ[O i] (η.app i).app (X, Y)) ∧
        HEq ((@inv _ _ _ _ (e.app i) (he i)).app (⟨X⟩, ⟨Y⟩))
          ((1 : Localization.Away (π i)) ⊗ₜ[O i] (inv (η.app i)).app (X, Y)))) := by
  rcases Q with ⟨QT, Qa, Qc⟩
  have eQ : @QT = fun i j h ↦ ScalarLocalization.extension (π i) (π j) (φ h)
      (unitImage h) (S.T h) (semi h) := by
    funext i j h
    exact hQ.1 h
  cases eQ
  rcases P with ⟨PT, Pa, Pc⟩
  have eP : @PT = fun i j h ↦ ScalarLocalization.extension (π i) (π j) (φ h)
      (unitImage h) (T.T h) (semiT h) := by
    funext i j h
    exact hP.1 h
  cases eP
  obtain ⟨F, hF⟩ := rational_family T semiT _ _ hQ hP U hU
  obtain ⟨G, hG⟩ := rational_family T semiT _ _ hQ hP V hV
  rcases F with ⟨FU, Fc, Ft⟩
  have eF : FU = fun i ↦ rawFunctor (π i) (U.U i) (hU i) := by
    funext i
    exact (hF.1 i).trans (raw_eq _ _ _)
  cases eF
  rcases G with ⟨GU, Gc, Gt⟩
  have eG : GU = fun i ↦ rawFunctor (π i) (V.U i) (hV i) := by
    funext i
    exact (hG.1 i).trans (raw_eq _ _ _)
  cases eG
  let e : Transformation ⟨_, Fc, Ft⟩ ⟨_, Gc, Gt⟩ :=
    ⟨(fun i ↦ rawNat (π i) (U.U i) (V.U i) (hU i) (hV i) (η.app i)), by
        intro i j h X Y
        rw [eq_of_heq (hF.2 h X.obj Y.obj).1,
          eq_of_heq (hG.2 h X.obj Y.obj).1]
        change tensorComp (O j) (B j) (π j) _ _ _
            (1 ⊗ₜ[O j] (V.comparison h).hom.app (X.obj, Y.obj))
            ((ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h)
              (T.T h) (semiT h)).map
              (1 ⊗ₜ[O i] (η.app i).app (X.obj, Y.obj))) =
          tensorComp (O j) (B j) (π j) _ _ _
            (1 ⊗ₜ[O j] (η.app j).app ((S.T h).obj X.obj, (S.T h).obj Y.obj))
            (1 ⊗ₜ[O j] (U.comparison h).hom.app (X.obj, Y.obj))
        rw [extension_tmul, map_one, tensorComp_tmul,
          tensorComp_tmul]
        simp only [one_mul]
        exact congrArg (fun f ↦ (1 : Localization.Away (π j)) ⊗ₜ[O j] f)
          (η.square h X.obj Y.obj)⟩
  have he (i : I) : IsIso (e.app i) := by
    let ei : rawFunctor (π i) (U.U i) (hU i) ≅ rawFunctor (π i) (V.U i) (hV i) :=
      NatIso.ofComponents
        (fun X ↦ (ScalarLocalization.localization (O i) (B i) (π i)).mapIso
          ((asIso (η.app i)).app (X.1.obj, X.2.obj)))
        (by intro X Y f; exact (e.app i).naturality f)
    have hm : ei.hom = e.app i := by
      apply NatTrans.ext
      rfl
    rw [← hm]
    exact ei.isIso_hom
  refine ⟨⟨_, Fc, Ft⟩, ⟨_, Gc, Gt⟩, e, hF, hG, he, ?_⟩
  intro i X Y
  refine ⟨HEq.rfl, ?_⟩
  have hi : inv (e.app i) =
      rawNat (π i) (V.U i) (U.U i) (hV i) (hU i) (inv (η.app i)) := by
    apply IsIso.inv_eq_of_hom_inv_id
    apply NatTrans.ext
    funext Z
    change tensorComp (O i) (B i) (π i) _ _ _
      (1 ⊗ₜ[O i] (inv (η.app i)).app (Z.1.obj, Z.2.obj))
      (1 ⊗ₜ[O i] (η.app i).app (Z.1.obj, Z.2.obj)) = 1 ⊗ₜ[O i] 𝟙 _
    rw [tensorComp_tmul, one_mul]
    exact congrArg (fun f ↦ (1 : Localization.Away (π i)) ⊗ₜ[O i] f)
      (NatTrans.congr_app (IsIso.hom_inv_id (η.app i)) (Z.1.obj, Z.2.obj))
  rw [hi]
  rfl

private theorem rational_unitComparison
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (φid : ∀ i, φ (le_refl i) = RingHom.id (O i))
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h'))
    (uS : Units S) (uT : Units T) (U : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    (unitU : HasUnitComparison U uS uS uT)
    (F : Family (rationalSystem π φ unitImage S semi φcomp)
      (rationalSystem π φ unitImage S semi φcomp)
      (rationalSystem π φ unitImage T semiT φcomp))
    (hF : IsRationalFamily U hU F) :
    HasUnitComparison F (rationalUnits π φ unitImage S semi φid φcomp uS)
      (rationalUnits π φ unitImage S semi φid φcomp uS)
      (rationalUnits π φ unitImage T semiT φid φcomp uT) := by
  rcases F with ⟨FU, Fc, Ft⟩
  have hFU : FU = fun i ↦ rawFunctor (π i) (U.U i) (hU i) := by
    funext i
    exact (hF.1 i).trans (raw_eq _ _ _)
  cases hFU
  intro i X Y
  rw [eq_of_heq (hF.2 (le_refl i) X.obj Y.obj).1]
  change tensorComp (O i) (B i) (π i) _ _ _
      (rawHom (π i) (U.U i) (hU i) _ _ _ _
        (1 ⊗ₜ[O i] (uS.unit i).hom.app X.obj)
        (1 ⊗ₜ[O i] (uS.unit i).hom.app Y.obj))
      (1 ⊗ₜ[O i] (U.comparison (le_refl i)).hom.app (X.obj, Y.obj)) =
    1 ⊗ₜ[O i] (uT.unit i).hom.app ((U.U i).obj (X.obj, Y.obj))
  rw [rawHom_tmul, one_mul, tensorComp_tmul, one_mul]
  exact congrArg (fun f ↦ (1 : Localization.Away (π i)) ⊗ₜ[O i] f)
    (unitU i X.obj Y.obj)

private theorem rationalSystem_spec
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h')) :
    IsRationalSystem π φ unitImage S semi
      (rationalSystem π φ unitImage S semi φcomp) := by
  exact ⟨fun _ ↦ rfl, fun _ _ _ ↦ ⟨HEq.rfl, HEq.rfl⟩⟩

private theorem rationalUnits_hom
    (φid : ∀ i, φ (le_refl i) = RingHom.id (O i))
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h')) (uS : Units S) (i : I) (X : A i) :
    HEq ((rationalUnits π φ unitImage S semi φid φcomp uS).unit i |>.hom.app ⟨X⟩)
      ((1 : Localization.Away (π i)) ⊗ₜ[O i] (uS.unit i).hom.app X) := by
  rfl

attribute [local irreducible] rationalSystem rationalUnits
  Units HasUnitComparison

private theorem rationalData [IsDirectedOrder I]
    (join : I → I → I) (left : ∀ i j, i ≤ join i j)
    (right : ∀ i j, j ≤ join i j)
    (φid : ∀ i, φ (le_refl i) = RingHom.id (O i))
    (φcomp : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (φ h').comp (φ h) = φ (h.trans h'))
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (uS : Units S) (uT : Units T) (U V : Family S S T)
    (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    (hV : ∀ i, IsSeparatelyLinear (O i) (V.U i))
    (unitU : HasUnitComparison U uS uS uT) (unitV : HasUnitComparison V uS uS uT)
    (η : Transformation U V) [∀ i, IsIso (η.app i)] :
    ∃ (Q : StageSystem (fun i ↦ ScalarLocalization (O i) (A i) (π i)))
      (P : StageSystem (fun i ↦ ScalarLocalization (O i) (B i) (π i)))
      (F G : Family Q Q P) (e : Transformation F G) (uQ : Units Q) (uP : Units P),
      IsRationalSystem π φ unitImage S semi Q ∧
      IsRationalSystem π φ unitImage T semiT P ∧
      IsRationalFamily U hU F ∧ IsRationalFamily V hV G ∧
      HasUnitComparison F uQ uQ uP ∧ HasUnitComparison G uQ uQ uP ∧
      (∀ i (X : A i), HEq ((uQ.unit i).hom.app ⟨X⟩)
        ((1 : Localization.Away (π i)) ⊗ₜ[O i] (uS.unit i).hom.app X)) ∧
      (∀ i (X : B i), HEq ((uP.unit i).hom.app ⟨X⟩)
        ((1 : Localization.Away (π i)) ⊗ₜ[O i] (uT.unit i).hom.app X)) ∧
      ∃ he : ∀ i, IsIso (e.app i),
      (∀ i (X Y : A i),
        HEq ((e.app i).app (⟨X⟩, ⟨Y⟩))
          ((1 : Localization.Away (π i)) ⊗ₜ[O i] (η.app i).app (X, Y)) ∧
        HEq ((@inv _ _ _ _ (e.app i) (he i)).app (⟨X⟩, ⟨Y⟩))
          ((1 : Localization.Away (π i)) ⊗ₜ[O i] (inv (η.app i)).app (X, Y))) ∧
        IsIso (descendTransformation F G e join left right) := by
  let Q := rationalSystem π φ unitImage S semi φcomp
  let P := rationalSystem π φ unitImage T semiT φcomp
  have hQ := rationalSystem_spec (π := π) (φ := φ) (unitImage := unitImage)
    (S := S) (semi := semi) φcomp
  have hP := rationalSystem_spec (π := π) (φ := φ) (unitImage := unitImage)
    (S := T) (semi := semiT) φcomp
  obtain ⟨F, G, e, hF, hG, he, heform⟩ :=
    rational_comparison (π := π) (φ := φ) (unitImage := unitImage)
      (S := S) (semi := semi) T semiT Q P hQ hP U V hU hV η
  let uQ := rationalUnits π φ unitImage S semi φid φcomp uS
  let uP := rationalUnits π φ unitImage T semiT φid φcomp uT
  have huQ := rationalUnits_hom (π := π) (φ := φ) (unitImage := unitImage)
    (S := S) (semi := semi) φid φcomp uS
  have huP := rationalUnits_hom (π := π) (φ := φ) (unitImage := unitImage)
    (S := T) (semi := semiT) φid φcomp uT
  have hfunit := rational_unitComparison (π := π) (φ := φ)
    (unitImage := unitImage) (S := S) (semi := semi) T semiT φid φcomp
    uS uT U hU unitU F hF
  have hgunit := rational_unitComparison (π := π) (φ := φ)
    (unitImage := unitImage) (S := S) (semi := semi) T semiT φid φcomp
    uS uT V hV unitV G hG
  exact ⟨Q, P, F, G, e, uQ, uP, hQ, hP, hF, hG, hfunit, hgunit,
    huQ, huP, he, heform, (descent_equations join left right).2.2 F G e he⟩

end RationalSystems

private theorem localization_unit_of_inclusion
    {R₀ S₀ K₀ L₀ : Type*} [CommRing R₀] [CommRing S₀] [CommRing K₀] [CommRing L₀]
    [Algebra R₀ K₀] [Algebra S₀ L₀] (p : R₀) (q : S₀)
    (φ : R₀ →+* S₀) (ι : K₀ →+* L₀)
    (hc : ∀ x, algebraMap S₀ L₀ (φ x) = ι (algebraMap R₀ K₀ x))
    (hp : IsUnit (algebraMap R₀ K₀ p)) (e : Localization.Away q ≃ₐ[S₀] L₀) :
    IsUnit (algebraMap S₀ (Localization.Away q) (φ p)) := by
  have hu : IsUnit (e (algebraMap S₀ (Localization.Away q) (φ p))) := by
    rw [e.commutes, hc]
    exact hp.map ι
  have hv := hu.map e.symm.toMonoidHom
  change IsUnit (e.symm (e _)) at hv
  simpa only [e.symm_apply_apply] using hv

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer


section PadicCoefficients

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The recorded valuation rings, indexed by the genuine finite intermediate extensions.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Integers (E : Padic.FiniteCoefficientFields l Ω) : Subring E.val :=
  Padic.coefficientExtensionIntegers l E.val

/-- The named integer ring is exactly the recorded coefficient-extension subring.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem Integers_eq (E : Padic.FiniteCoefficientFields l Ω) :
    Integers l Ω E = Padic.coefficientExtensionIntegers l E.val := by
  exact Eq.trans rfl rfl

/-- Cache the recorded valuation ring's commutative-ring instance.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
instance integersCommRing (E : Padic.FiniteCoefficientFields l Ω) :
    CommRing (Integers l Ω E) :=
  Subring.toCommRing (Integers l Ω E)

attribute [local implicit_reducible] integersCommRing

/-- Cache the canonical valuation-subring algebra structure on its coefficient field.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
instance integersAlgebra (E : Padic.FiniteCoefficientFields l Ω) :
    Algebra (Integers l Ω E) E.val :=
  @Algebra.ofSubsemiring E.val E.val _ _ (Algebra.id E.val)
    (Subring E.val) _ _ (Integers l Ω E)

attribute [local implicit_reducible] integersAlgebra

/-- The recorded uniformizer belongs to the named integer subring.
Source: the coefficient uniformizer definition and `Integers_eq`
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem uniformizer_mem (E : Padic.FiniteCoefficientFields l Ω) :
    (Padic.coefficientExtensionUniformizer l E.val : E.val) ∈ Integers l Ω E := by
  rw [Integers_eq]
  exact (Padic.coefficientExtensionUniformizer l E.val).property

/-- The recorded uniformizer; no extra torsion-free or characteristic hypotheses.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def uniformizer (E : Padic.FiniteCoefficientFields l Ω) : Integers l Ω E :=
  ⟨(Padic.coefficientExtensionUniformizer l E.val : E.val), uniformizer_mem l Ω E⟩

/-- The named uniformizer has the recorded coefficient-field value.
Source: the specified uniformizer construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem uniformizer_val (E : Padic.FiniteCoefficientFields l Ω) :
    (uniformizer l Ω E : E.val) = (Padic.coefficientExtensionUniformizer l E.val : E.val) := by
  exact Eq.trans rfl rfl

private theorem integerInclusion_absoluteValue
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (x : E.val) :
    Padic.coefficientExtensionAbsoluteValue l L.val (IntermediateField.inclusion h x) =
      Padic.coefficientExtensionAbsoluteValue l E.val x := by
  let ι := IntermediateField.inclusion h
  let f : AbsoluteValue E.val ℝ :=
    (Padic.coefficientExtensionAbsoluteValue l L.val).comp ι.toRingHom.injective
  have hf : ∀ a : Padic l, f (algebraMap (Padic l) E.val a) = ‖a‖ := by
    intro a
    change Padic.coefficientExtensionAbsoluteValue l L.val
      (ι (algebraMap (Padic l) E.val a)) = ‖a‖
    rw [ι.commutes]
    exact spectralNorm_extends a
  exact spectralNorm_unique_field_norm_ext hf x

/-- The field inclusion preserves the recorded valuation subrings.
Source: spectral-norm uniqueness and the defining DVR membership formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof: the absolute value on the larger field restricts to the unique extension
of the p-adic absolute value on the smaller field. Integer-ring membership is
absolute value at most one in both fields, so the restriction preserves it. -/
theorem integerInclusion_mem {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (x : Integers l Ω E) :
    IntermediateField.inclusion h (x : E.val) ∈ Integers l Ω L := by
  have hE := (Padic.extension_integers_dvr l E.val
    (Padic.coefficientExtensionAbsoluteValue l E.val)
    (spectralNorm_extends (K := Padic l) (L := E.val))).choose_spec.choose_spec.1 (x : E.val)
  have hL := (Padic.extension_integers_dvr l L.val
    (Padic.coefficientExtensionAbsoluteValue l L.val)
    (spectralNorm_extends (K := Padic l) (L := L.val))).choose_spec.choose_spec.1
      (IntermediateField.inclusion h (x : E.val))
  have hx : Padic.coefficientExtensionAbsoluteValue l E.val (x : E.val) ≤ 1 := by
    apply hE.mp
    simpa only [Integers, Padic.coefficientExtensionIntegers] using x.property
  rw [← integerInclusion_absoluteValue l Ω h (x : E.val)] at hx
  simpa only [Integers, Padic.coefficientExtensionIntegers] using hL.mpr hx

/-- The canonical integer-ring restriction of the given intermediate-field inclusion.
Source: common-stage coefficient formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def integerInclusion {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    Integers l Ω E →+* Integers l Ω L :=
  ((IntermediateField.inclusion h).toRingHom.comp
    (Integers l Ω E).subtype).codRestrict
      (Integers l Ω L) (integerInclusion_mem l Ω h)

/-- The integer-ring map acts by the given intermediate-field inclusion.
Source: restriction of the actual field inclusion
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem integerInclusion_apply {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (x : Integers l Ω E) :
    (integerInclusion l Ω h x : L.val) = IntermediateField.inclusion h (x : E.val) := by
  exact Eq.trans rfl rfl

set_option linter.unusedSectionVars false in
/-- The exact p-adic specialization of the coefficient hypotheses used by rational_system.
Source: both coefficient formulas (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 4: the inclusions are restrictions of the actual field inclusions, so identity
and tower laws hold pointwise. A uniformizer is nonzero; its image is invertible in L.
lem-weil-l-adic-integers-localization-uniformizer identifies L with its recorded localization,
so it is invertible there as well. The recorded algebra equivalence gives the actual E-Hom
tensor model; TensorProduct.comm exchanges its scalar-first and Hom-first conventions. -/
theorem coefficient_hypotheses :
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      integerInclusion l Ω (le_refl E) = RingHom.id (Integers l Ω E)) ∧
    (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ M),
      (integerInclusion l Ω k).comp (integerInclusion l Ω h) =
        integerInclusion l Ω (h.trans k)) ∧
    (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L),
      IsUnit (algebraMap (Integers l Ω L) (Localization.Away (uniformizer l Ω L))
        (integerInclusion l Ω h (uniformizer l Ω E)))) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      Nonempty (Localization.Away (uniformizer l Ω E) ≃ₐ[Integers l Ω E] E.val)) := by
  have hloc (E : Padic.FiniteCoefficientFields l Ω) :
      IsLocalization.Away (uniformizer l Ω E) E.val := by
    dsimp only [Integers, uniformizer, integersCommRing, integersAlgebra]
    exact (Padic.coefficientExtension_localization_uniformizer.{w, 0} l E.val).1
  have hmodel (E : Padic.FiniteCoefficientFields l Ω) :
      Nonempty (Localization.Away (uniformizer l Ω E) ≃ₐ[Integers l Ω E] E.val) := by
    obtain ⟨e, _⟩ := (Padic.coefficientExtension_localization_uniformizer.{w, 0} l E.val).2
    refine ⟨?_⟩
    dsimp only [Integers, uniformizer, integersCommRing, integersAlgebra]
    exact e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    ext x
    unfold integerInclusion
    rfl
  · intro E L M h k
    ext x
    unfold integerInclusion
    rfl
  · intro E L h
    obtain ⟨e⟩ := hmodel L
    let : IsLocalization.Away (uniformizer l Ω E) E.val := hloc E
    exact localization_unit_of_inclusion
      (R₀ := Integers l Ω E) (S₀ := Integers l Ω L) (K₀ := E.val) (L₀ := L.val)
      (uniformizer l Ω E) (uniformizer l Ω L) (integerInclusion l Ω h)
      (IntermediateField.inclusion h).toRingHom (fun _ ↦ rfl)
      (IsLocalization.Away.algebraMap_isUnit (S := E.val) (uniformizer l Ω E)) e
  · exact hmodel

attribute [local irreducible] Padic.finiteCoefficientCompositum uniformizer integerInclusion

/-- The chosen output field is exactly the compositum, including the base-field case.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 5: finiteCoefficientFields_properties supplies both upper-bound proofs;
finiteCoefficientCompositum is the supremum of intermediate fields, hence is finite. -/
theorem compositum_upper :
    (∀ E F : Padic.FiniteCoefficientFields l Ω,
      E ≤ Padic.finiteCoefficientCompositum l Ω E F) ∧
    (∀ E F : Padic.FiniteCoefficientFields l Ω,
      F ≤ Padic.finiteCoefficientCompositum l Ω E F) := by
  exact ⟨fun E F ↦ (Padic.finiteCoefficientFields_properties l Ω).1 E F |>.1,
    fun E F ↦ (Padic.finiteCoefficientFields_properties l Ω).1 E F |>.2⟩

/-- Directedness uses the actual finite compositum, not finiteness of the field as a set.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
instance coefficientDirected : IsDirectedOrder (Padic.FiniteCoefficientFields l Ω) where
  directed E F := ⟨Padic.finiteCoefficientCompositum l Ω E F,
    (compositum_upper l Ω).1 E F, (compositum_upper l Ω).2 E F⟩



/-- Bilinear comparison descent for the stated p-adic coefficient families.
Source: main-20261015 def-weil-rationalization-karoubi, displayed Hom tensor E formula;
def-weil-algebraically-closed-coefficients, displayed common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof: (1) factor the bifunctor arrow operation into its two slots and base change its
bilinear Hom map (def-weil-module-base-change). (2) Check identities and composition on
pure tensors, then extend by additivity; tensor generation gives uniqueness.
(3) Tensor η and its inverse with one; naturality is the integral square times ab.
(4) Extend transitions semilinearly (lem-pur-semilinear-scalar-localization); the image
of a uniformizer is invertible by lem-weil-l-adic-integers-localization-uniformizer.
Tensor all unit, tower, λ and scalar-square component equations with one.
(5) Finite composita give common upper fields. Transport uses conjugation by the
supplied associators (def-weil-finite-subextension-directed-set).
(6) Use the existing StageSystem quotient calculus. The diagonal from the product
stage system is fully faithful by common-stage representatives and eventual equality.
(7) At L identify each output with its two input extensions using endpoint, then
conjugate U_L(f,g). (8) The λ tower equation and input associator cocycles imply that
this formula commutes with transport. (9) Equal representatives become equal later;
identity and composition follow by cancellation of endpoint isomorphisms.
(10) The scalar square identifies the displayed component with S^D(η_K), so every L
represents the same class; use the inverse square for the inverse class.
(11) Naturality follows from η_L after cancelling endpoints; a different initial field
is compared at a further common field by change_common_field.
(12) Identity and vertical composition cancel middle endpoint factors. Output whiskering
uses F(d)μ=d_FU. Input whiskering uses U(μ,1), or U(1,μ), to compare its differing
objects, as in whisker_input_left/right; the same calculation applies to nested slots.
(13) Choose a common field for every finite equation and apply finite_equation_descent.
Additivity includes signs. No Hom injectivity, additive objects, or idempotent completion
is used. The accompanying raw_equations and whiskering declarations state the equation
preservation clauses on arbitrary supplied compatible families. -/
theorem bilinear_comparison_coefficient_descent
    {A : Padic.FiniteCoefficientFields l Ω → Type u} [∀ E, Category.{v} (A E)]
    [∀ E, Preadditive (A E)] [∀ E, Linear (Integers l Ω E) (A E)]
    {B : Padic.FiniteCoefficientFields l Ω → Type u'} [∀ E, Category.{v'} (B E)]
    [∀ E, Preadditive (B E)] [∀ E, Linear (Integers l Ω E) (B E)]
    (S : StageSystem A) (T : StageSystem B)
    [∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L), (S.T h).Additive]
    [∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L), (T.T h).Additive]
    (semiS : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      ScalarLocalization.IsSemilinear (integerInclusion l Ω h) (S.T h))
    (semiT : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      ScalarLocalization.IsSemilinear (integerInclusion l Ω h) (T.T h))
    (uS : Units S) (uT : Units T) (U V : Family S S T)
    (hU : ∀ E, IsSeparatelyLinear (Integers l Ω E) (U.U E))
    (hV : ∀ E, IsSeparatelyLinear (Integers l Ω E) (V.U E))
    (unitU : HasUnitComparison U uS uS uT) (unitV : HasUnitComparison V uS uS uT)
    (η : Transformation U V) [∀ E, IsIso (η.app E)] :
    ∃ (Q : StageSystem (fun E ↦ ScalarLocalization (Integers l Ω E) (A E)
          (uniformizer l Ω E)))
      (P : StageSystem (fun E ↦ ScalarLocalization (Integers l Ω E) (B E)
          (uniformizer l Ω E)))
      (F G : Family Q Q P) (e : Transformation F G) (uQ : Units Q) (uP : Units P),
      IsRationalSystem (uniformizer l Ω) (integerInclusion l Ω)
        (fun h ↦ (coefficient_hypotheses l Ω).2.2.1 _ _ h) S semiS Q ∧
      IsRationalSystem (uniformizer l Ω) (integerInclusion l Ω)
        (fun h ↦ (coefficient_hypotheses l Ω).2.2.1 _ _ h) T semiT P ∧
      IsRationalFamily U hU F ∧ IsRationalFamily V hV G ∧
      HasUnitComparison F uQ uQ uP ∧ HasUnitComparison G uQ uQ uP ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω) (X : A E),
        HEq ((uQ.unit E).hom.app ⟨X⟩)
          ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[Integers l Ω E]
            (uS.unit E).hom.app X)) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω) (X : B E),
        HEq ((uP.unit E).hom.app ⟨X⟩)
          ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[Integers l Ω E]
            (uT.unit E).hom.app X)) ∧
      ∃ he : ∀ E, IsIso (e.app E),
      (∀ (E : Padic.FiniteCoefficientFields l Ω) (X Y : A E),
        HEq ((e.app E).app (⟨X⟩, ⟨Y⟩))
          ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[Integers l Ω E]
            (η.app E).app (X, Y)) ∧
        HEq ((@inv _ _ _ _ (e.app E) (he E)).app (⟨X⟩, ⟨Y⟩))
          ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[Integers l Ω E]
            (inv (η.app E)).app (X, Y))) ∧
      IsIso (descendTransformation F G e (Padic.finiteCoefficientCompositum l Ω)
        ((compositum_upper l Ω).1) ((compositum_upper l Ω).2)) := by
  exact rationalData (I := Padic.FiniteCoefficientFields l Ω) (O := fun E ↦ ↥(Integers l Ω E))
    (A := A) (B := B) (π := uniformizer l Ω) (φ := integerInclusion l Ω)
    (unitImage := fun h ↦ (coefficient_hypotheses l Ω).2.2.1 _ _ h)
    (S := S) (semi := semiS) (Padic.finiteCoefficientCompositum l Ω)
    ((compositum_upper l Ω).1) ((compositum_upper l Ω).2)
    (coefficient_hypotheses l Ω).1
    (fun h k ↦ (coefficient_hypotheses l Ω).2.1 _ _ _ h k)
    T semiT uS uT U V hU hV unitU unitV η

end PadicCoefficients
end CategoryTheory.BilinearCoefficientDescent
