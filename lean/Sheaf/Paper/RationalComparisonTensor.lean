/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonStructures
public import Sheaf.Paper.RationalComparisonFunctor
public import Sheaf.Paper.PerfectScalarMonoidalFunctor

/-! # The rational tensor comparison on the concrete balanced functor

Source: blueprint order 1826, conditional construction steps 3 and 4
(blueprint: lem-sf-rational-comparison-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures.TensorComparisonDescent
attribute [local semireducible] FieldOf integerRing
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]
variable {C} (A : IntegralData C) (hA : A.Valid)

/-- The integral comparison followed by fraction-field extension is strong monoidal. -/
@[irreducible] def fractionFunctorCore (E : Index l Ω) :
    (fractionFunctor A E).CoreMonoidal :=
  DerivedCategory.PerfectScalar.perfectCompositeCore (A.F E) (A.perfect E) (A.tensor E)
    (fractionMap l Ω E)

attribute [local instance] rationalStructures

/-- The integral tensor comparison extends to the actual rational Hom modules. -/
@[irreducible] def rationalFunctorCore (E : Index l Ω) : (rationalFunctor A hA E).CoreMonoidal where
  εIso := (fractionFunctorCore A E).εIso
  μIso X Y := (fractionFunctorCore A E).μIso X.obj Y.obj
  μIso_hom_natural_left := by
    intro X Y f Z
    change rationalHom A hA E X.obj Y.obj f ▷ (fractionFunctor A E).obj Z.obj ≫ _ =
      _ ≫ rationalHom A hA E _ _
        (ScalarLocalization.tensorMap _ _ _ f (1 ⊗ₜ[Integers l Ω E] 𝟙 Z.obj))
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
        ScalarLocalization.tensorMap_add_left, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      simp only [ScalarLocalization.tensorMap_tmul, mul_one, rationalHom_tmul,
        tensorHom_id, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]
      congr 1
      exact (fractionFunctorCore A E).μIso_hom_natural_left f Z.obj
  μIso_hom_natural_right := by
    intro X Y Z f
    change (fractionFunctor A E).obj Z.obj ◁ rationalHom A hA E X.obj Y.obj f ≫ _ =
      _ ≫ rationalHom A hA E _ _
        (ScalarLocalization.tensorMap _ _ _ (1 ⊗ₜ[Integers l Ω E] 𝟙 Z.obj) f)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add, MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp,
        ScalarLocalization.tensorMap_add_right, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      simp only [ScalarLocalization.tensorMap_tmul, one_mul, rationalHom_tmul,
        id_tensorHom, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]
      congr 1
      exact (fractionFunctorCore A E).μIso_hom_natural_right Z.obj f
  associativity X Y Z := by
    change _ ≫ _ ≫ rationalHom A hA E _ _
      (1 ⊗ₜ[Integers l Ω E] (α_ X.obj Y.obj Z.obj).hom) = _
    simp only [rationalHom_tmul, map_one, one_smul]
    exact (fractionFunctorCore A E).associativity X.obj Y.obj Z.obj
  left_unitality X := by
    change _ = _ ≫ _ ≫ rationalHom A hA E _ _
      (1 ⊗ₜ[Integers l Ω E] (λ_ X.obj).hom)
    simp only [rationalHom_tmul, map_one, one_smul]
    exact (fractionFunctorCore A E).left_unitality X.obj
  right_unitality X := by
    change _ = _ ≫ _ ≫ rationalHom A hA E _ _
      (1 ⊗ₜ[Integers l Ω E] (ρ_ X.obj).hom)
    simp only [rationalHom_tmul, map_one, one_smul]
    exact (fractionFunctorCore A E).right_unitality X.obj


end WeilConjectures.TensorComparisonDescent
