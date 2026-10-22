/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonStructures
public import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-! # The concrete rational coefficient transitions

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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

/-- The integral-field coefficient square commutes on actual elements.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem coefficientSquare {E L : Index l Ω} (a : E ≤ L) (r : Integers l Ω E) :
    (fieldMap l Ω a).hom (algebraMap (Integers l Ω E) (FieldOf l Ω E) r) =
      algebraMap (Integers l Ω L) (FieldOf l Ω L) ((integerMap l Ω a).hom r) := rfl

/-- The source uniformizer becomes invertible in the target raw localization.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem transitionInverts {E L : Index l Ω} (a : E ≤ L) :
    IsUnit (algebraMap (Integers l Ω L) (Localization.Away (uniformizer l Ω L))
      ((integerMap l Ω a).hom (uniformizer l Ω E))) := by
  apply (MulEquiv.isUnit_map (coefficientEquiv l Ω L).toMulEquiv).mp
  change IsUnit (coefficientEquiv l Ω L
    (algebraMap (Integers l Ω L) (Localization.Away (uniformizer l Ω L))
      ((integerMap l Ω a).hom (uniformizer l Ω E))))
  rw [AlgEquiv.commutes, ← coefficientSquare]
  have hu := (IsLocalization.Away.algebraMap_isUnit (uniformizer l Ω E)
    (S := Localization.Away (uniformizer l Ω E))).map (coefficientEquiv l Ω E).toRingHom
  change IsUnit (coefficientEquiv l Ω E
    (algebraMap (Integers l Ω E) (Localization.Away (uniformizer l Ω E))
      (uniformizer l Ω E))) at hu
  rw [AlgEquiv.commutes] at hu
  exact hu.map (fieldMap l Ω a).hom

/-- The induced coefficient map has exactly the prescribed field-inclusion formula.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem transitionCoefficient {E L : Index l Ω} (a : E ≤ L) :
    ScalarLocalization.coefficientMap (uniformizer l Ω E) (uniformizer l Ω L)
      (integerMap l Ω a).hom (transitionInverts a) =
      (coefficientEquiv l Ω L).symm.toRingHom.comp
        ((fieldMap l Ω a).hom.comp (coefficientEquiv l Ω E).toRingHom) := by
  symm
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
  ext r
  apply (coefficientEquiv l Ω L).injective
  change coefficientEquiv l Ω L ((coefficientEquiv l Ω L).symm
      ((fieldMap l Ω a).hom (coefficientEquiv l Ω E
        (algebraMap (Integers l Ω E) (Localization.Away (uniformizer l Ω E)) r)))) =
    coefficientEquiv l Ω L (algebraMap (Integers l Ω L)
      (Localization.Away (uniformizer l Ω L)) ((integerMap l Ω a).hom r))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
  exact coefficientSquare a r

include hA in
/-- The original transition is semilinear on every integral Hom module.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem integralTransitionSemilinear {E L : Index l Ω} (a : E ≤ L) :
    ScalarLocalization.IsSemilinear (integerMap l Ω a).hom (A.S.T a) := by
  intro X Y r f
  exact hA.hypothesis6 a X Y r f

/-- The rational transition is the existing, uniquely specified semilinear extension.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
def rationalTransition {E L : Index l Ω} (a : E ≤ L) : Rat C E ⥤ Rat C L := by
  letI := hA.hypothesis5 a
  exact ScalarLocalization.extension (uniformizer l Ω E) (uniformizer l Ω L)
    (integerMap l Ω a).hom (transitionInverts a) (A.S.T a)
    (integralTransitionSemilinear A hA a)

/-- The rational transition preserves addition.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem rationalTransition_additive {E L : Index l Ω} (a : E ≤ L) :
    (rationalTransition A hA a).Additive := by
  letI := hA.hypothesis5 a
  change (ScalarLocalization.extension _ _ _ _ (A.S.T a)
    (integralTransitionSemilinear A hA a)).Additive
  infer_instance

/-- On pure morphisms it multiplies the integral transition by the field-included scalar.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem rationalTransition_tmul {E L : Index l Ω} (a : E ≤ L) (X Y : Rat C E)
    (b : Localization.Away (uniformizer l Ω E)) (f : X.obj ⟶ Y.obj) :
    (rationalTransition A hA a).map (b ⊗ₜ[Integers l Ω E] f : X ⟶ Y) =
      (coefficientEquiv l Ω L).symm
        ((fieldMap l Ω a).hom (coefficientEquiv l Ω E b)) ⊗ₜ[Integers l Ω L]
          (A.S.T a).map f := by
  letI := hA.hypothesis5 a
  change ScalarLocalization.extensionHom _ _ _ _ _ _ _ _ _ = _
  unfold ScalarLocalization.extensionHom
  rw [(ScalarLocalization.existsUnique_semilinearHom (uniformizer l Ω E)
    (uniformizer l Ω L) (integerMap l Ω a).hom (transitionInverts a)
    (A.S.T a) (integralTransitionSemilinear A hA a) X.obj Y.obj).exists.choose_spec]
  rw [transitionCoefficient]
  rfl


/-- The additive Hom map underlying the concrete rational transition.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
def rationalTransitionHom {E L : Index l Ω} (a : E ≤ L) (X Y : C E) :
    (Localization.Away (uniformizer l Ω E) ⊗[Integers l Ω E] (X ⟶ Y)) →+
      (Localization.Away (uniformizer l Ω L) ⊗[Integers l Ω L]
        ((A.S.T a).obj X ⟶ (A.S.T a).obj Y)) := by
  letI := hA.hypothesis5 a
  exact ScalarLocalization.extensionHom (uniformizer l Ω E) (uniformizer l Ω L)
    (integerMap l Ω a).hom (transitionInverts a) (A.S.T a)
    (integralTransitionSemilinear A hA a) X Y

/-- The functor uses exactly this additive Hom map.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
theorem rationalTransition_map {E L : Index l Ω} (a : E ≤ L) (X Y : Rat C E)
    (f : X ⟶ Y) : (rationalTransition A hA a).map f =
      rationalTransitionHom A hA a X.obj Y.obj f := rfl

/-- The Hom map has the specified pure-tensor value.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition). -/
@[simp] theorem rationalTransitionHom_tmul {E L : Index l Ω} (a : E ≤ L) (X Y : C E)
    (b : Localization.Away (uniformizer l Ω E)) (f : X ⟶ Y) :
    rationalTransitionHom A hA a X Y (b ⊗ₜ[Integers l Ω E] f) =
      (coefficientEquiv l Ω L).symm
        ((fieldMap l Ω a).hom (coefficientEquiv l Ω E b)) ⊗ₜ[Integers l Ω L]
          (A.S.T a).map f :=
  rationalTransition_tmul A hA a ⟨X⟩ ⟨Y⟩ b f


end WeilConjectures.TensorComparisonDescent
