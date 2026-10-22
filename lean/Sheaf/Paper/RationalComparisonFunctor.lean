/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalTensorComparisonSystem

/-! # The balanced rational comparison functor

Source: the conditional scalar descent argument, steps 1 and 3
(blueprint: lem-sf-rational-comparison-functor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u c h

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace WeilConjectures.TensorComparisonDescent

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]
variable {C} (A : IntegralData C) (hA : A.Valid)

/-- The original comparison followed by actual derived scalar extension. -/
def fractionFunctor (E : Index l Ω) : C E ⥤ D (FieldOf l Ω E) :=
  A.F E ⋙ fractionB l Ω E

include hA in
/-- Additivity holds on the perfect image of the integral comparison. -/
theorem fractionFunctor_additive (E : Index l Ω) : (fractionFunctor A E).Additive where
  map_add {X Y} {f g} := by
    change (fractionB l Ω E).map ((A.F E).map (f + g)) = _
    letI := hA.hypothesis2 E
    rw [Functor.map_add]
    exact DerivedCategory.PerfectScalar.coherenceData.additive
      (fractionMap l Ω E) _ _ (A.perfect E X) (A.perfect E Y) _ _

include hA in
/-- Scalar linearity holds on the same perfect image. -/
theorem fractionFunctor_smul (E : Index l Ω) {X Y : C E}
    (r : Integers l Ω E) (f : X ⟶ Y) :
    (fractionFunctor A E).map (r • f) =
      algebraMap (Integers l Ω E) (FieldOf l Ω E) r • (fractionFunctor A E).map f := by
  letI := hA.hypothesis2 E
  letI := hA.hypothesis3 E
  change (fractionB l Ω E).map ((A.F E).map (r • f)) = _
  rw [Functor.map_smul]
  exact DerivedCategory.PerfectScalar.coherenceData.linear
    (fractionMap l Ω E) _ _ (A.perfect E X) (A.perfect E Y) r _

/-- The scalar-balanced Hom map; its definition is an actual tensor lift. -/
def rationalHom (E : Index l Ω) (X Y : C E) :
    (Localization.Away (uniformizer l Ω E) ⊗[Integers l Ω E] (X ⟶ Y)) →+
      ((fractionFunctor A E).obj X ⟶ (fractionFunctor A E).obj Y) := by
  letI := fractionFunctor_additive A hA E
  let β : Localization.Away (uniformizer l Ω E) →+ (X ⟶ Y) →+
      ((fractionFunctor A E).obj X ⟶ (fractionFunctor A E).obj Y) :=
    { toFun := fun a ↦
        { toFun := fun f ↦ coefficientEquiv l Ω E a • (fractionFunctor A E).map f
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      map_zero' := by ext f; simp
      map_add' := by intros; ext f; simp [add_smul] }
  refine TensorProduct.liftAddHom β ?_
  intro r a f
  dsimp only [β, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [fractionFunctor_smul A hA, smul_smul]
  congr 1
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, mul_comm]

@[simp] theorem rationalHom_tmul (E : Index l Ω) (X Y : C E)
    (a : Localization.Away (uniformizer l Ω E)) (f : X ⟶ Y) :
    rationalHom A hA E X Y (a ⊗ₜ[Integers l Ω E] f) =
      coefficientEquiv l Ω E a • (fractionFunctor A E).map f := by
  simp only [rationalHom, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Functoriality of the explicitly balanced rational Hom maps. -/
theorem rationalHom_comp (E : Index l Ω) (X Y Z : C E)
    (f : Localization.Away (uniformizer l Ω E) ⊗[Integers l Ω E] (X ⟶ Y))
    (g : Localization.Away (uniformizer l Ω E) ⊗[Integers l Ω E] (Y ⟶ Z)) :
    rationalHom A hA E X Z
        (ScalarLocalization.composition (Integers l Ω E) (C E) (uniformizer l Ω E)
          X Y Z g f) =
      rationalHom A hA E X Y f ≫ rationalHom A hA E Y Z g := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, hf, hf', Preadditive.add_comp]
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp [LinearMap.zero_apply]
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, hg, hg', Preadditive.comp_add]
    | tmul b g =>
      rw [ScalarLocalization.composition_tmul]
      simp only [rationalHom_tmul, map_mul, Functor.map_comp,
        Linear.smul_comp, Linear.comp_smul, smul_smul]

/-- Rationalization uses the balanced Hom lift, not an unspecified existence witness. -/
def rationalFunctor (E : Index l Ω) : Rat C E ⥤ D (FieldOf l Ω E) where
  obj X := (fractionFunctor A E).obj X.obj
  map {X Y} f := rationalHom A hA E X.obj Y.obj f
  map_id X := by
    change rationalHom A hA E X.obj X.obj (1 ⊗ₜ[Integers l Ω E] 𝟙 X.obj) = _
    simp only [rationalHom_tmul, map_one, one_smul]
    exact (fractionFunctor A E).map_id X.obj
  map_comp {X Y Z} f g := rationalHom_comp A hA E X.obj Y.obj Z.obj f g

/-- The actual rational functor has the prescribed arrow formula. -/
@[simp] theorem rationalFunctor_map_tmul (E : Index l Ω) (X Y : Rat C E)
    (a : Localization.Away (uniformizer l Ω E)) (f : X.obj ⟶ Y.obj) :
    (rationalFunctor A hA E).map (a ⊗ₜ[Integers l Ω E] f : X ⟶ Y) =
      coefficientEquiv l Ω E a • (fractionB l Ω E).map ((A.F E).map f) :=
  rationalHom_tmul A hA E X.obj Y.obj a f

/-- The rational functor preserves sums by the tensor-lift construction. -/
theorem rationalFunctor_additive (E : Index l Ω) : (rationalFunctor A hA E).Additive where
  map_add := (rationalHom A hA E _ _).map_add _ _

/-- Perfectness is preserved by actual derived scalar extension. -/
theorem rationalFunctor_perfect (E : Index l Ω) (X : Rat C E) :
    DerivedCategory.IsPerfectRingComplex ((rationalFunctor A hA E).obj X) :=
  DerivedCategory.PerfectScalar.coherenceData.preserves
    (fractionMap l Ω E) _ (A.perfect E X.obj)

/-- Over a field a perfect complex has bounded finite-dimensional cohomology. -/
theorem perfect_pointFiniteDimensional (K : Type u) [Field K]
    (P : D K) (hP : DerivedCategory.IsPerfectRingComplex P) :
    DerivedCategory.pointFiniteDimensional K P := by
  have hp : P.IsPerfect := hP
  obtain ⟨a, b, ha, hb⟩ := hp.exists_homologyConcentratedIn
  constructor
  · refine ⟨Finset.Icc a b, fun i hi ↦ ?_⟩
    by_cases hia : i < a
    · exact P.isZero_of_isGE a i hia
    · have hbi : b < i := by
        have hn : ¬ (a ≤ i ∧ i ≤ b) := by simpa only [Finset.mem_Icc] using hi
        omega
      exact P.isZero_of_isLE b i hbi
  · intro i
    exact hp.finite_homology i

/-- The same concrete rational functor lands in the finite-dimensional stages. -/
theorem rationalFunctor_finite (E : Index l Ω) (X : Rat C E) :
    DerivedCategory.pointFiniteDimensional (FieldOf l Ω E) ((rationalFunctor A hA E).obj X) :=
  perfect_pointFiniteDimensional (FieldOf l Ω E) _ (rationalFunctor_perfect A hA E X)

end WeilConjectures.TensorComparisonDescent
