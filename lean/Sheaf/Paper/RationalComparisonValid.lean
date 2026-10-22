/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonDatum
import Sheaf.Paper.RationalComparisonNormalization

/-! # Normalized equations for the concrete rational comparison

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-valid).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
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


attribute [local instance] rationalStructures

/-- Assemble validity from only the remaining normalized scalar equations. -/
private theorem rationalDatum_valid_of_equations
    (h10 : RationalData.condition10 C A (rationalDatum A hA))
    (h11 : RationalData.condition11 C A (rationalDatum A hA))
    (h12 : RationalData.condition12 C A (rationalDatum A hA))
    (h23 : RationalData.condition23 C A (rationalDatum A hA))
    (h24 : RationalData.condition24 C A (rationalDatum A hA))
    (h25 : RationalData.condition25 C A (rationalDatum A hA))
    (h30 : RationalData.condition30 C A (rationalDatum A hA))
    (h31 : RationalData.condition31 C A (rationalDatum A hA)) :
    RationalData.Valid C A (rationalDatum A hA) := by
  unfold rationalDatum at h10 h11 h12 h23 h24 h25 h30 h31 ⊢
  exact {
  bilinear := rationalStructures_bilinear C
  tensorObject := rationalStructures_tensorObject C
  unitObject := rationalStructures_unitObject C
  tensorArrow := rationalStructures_tensorArrow C
  associator := rationalStructures_associator C
  symmetry := rationalStructures_symmetry C
  leftUnitor := rationalStructures_leftUnitor C
  rightUnitor := rationalStructures_rightUnitor C
  additive := rationalFunctor_additive A hA
  arrow E X Y f a := heq_of_eq (rationalFunctor_map_tmul A hA E X Y a f)
  tensorFormula := h10
  unitFormula := h11
  symmetric := h12
  transitionArrow a X Y f b := heq_of_eq (rationalTransition_tmul A hA a X Y b f)
  transitionAdditive := rationalTransition_additive A hA
  transitionTensor _ _ _ := HEq.rfl
  transitionUnit _ := HEq.rfl
  transitionSymmetric := by
    intro E L a X Y
    change ScalarLocalization.composition _ _ _ _ _ _
      (1 ⊗ₜ[Integers l Ω L] ((A.transitionTensor a).μIso Y.obj X.obj).inv)
      ((rationalTransition A hA a).map
        (1 ⊗ₜ[Integers l Ω E] (β_ X.obj Y.obj).hom)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[Integers l Ω L]
          (β_ ((A.S.T a).obj X.obj) ((A.S.T a).obj Y.obj)).hom)
        (1 ⊗ₜ[Integers l Ω L] ((A.transitionTensor a).μIso X.obj Y.obj).inv)
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      AlgEquiv.symm_apply_apply, ScalarLocalization.composition_tmul, one_mul]
    congr 1
    exact hA.hypothesis7 a X.obj Y.obj
  identity _ _ := HEq.rfl
  tower _ _ _ := HEq.rfl
  leftIdentity := by
    intro E L a X
    change (1 ⊗ₜ[Integers l Ω L] (A.S.assoc (le_refl E) a).hom.app X.obj) =
      (rationalTransition A hA a).map
        (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app X.obj)
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      AlgEquiv.symm_apply_apply]
    congr 1
    exact hA.hypothesis8 a X.obj
  rightIdentity := by
    intro E L a X
    change (1 ⊗ₜ[Integers l Ω L] (A.S.assoc a (le_refl L)).hom.app X.obj) =
      (1 ⊗ₜ[Integers l Ω L] (A.identity L).hom.app ((A.S.T a).obj X.obj))
    congr 1
    exact hA.hypothesis9 a X.obj
  kappaModel a P := DerivedCategory.PerfectScalar.fieldScalarComparison_model _ P
  phiFormula := h23
  phiIdentity := h24
  phiTower := h25
  identityTensor := by
    intro E X Y
    change ScalarLocalization.composition _ _ _ _ _ _
      (ScalarLocalization.tensorMap _ _ _
        (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app X.obj)
        (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app Y.obj))
      (1 ⊗ₜ[Integers l Ω E] ((A.transitionTensor (le_refl E)).μIso X.obj Y.obj).inv) =
      (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app (X.obj ⊗ Y.obj))
    simp only [ScalarLocalization.tensorMap_tmul, ScalarLocalization.composition_tmul, one_mul]
    congr 1
    exact hA.hypothesis10 E X.obj Y.obj
  identityUnit := by
    intro E
    change (1 ⊗ₜ[Integers l Ω E] (A.transitionTensor (le_refl E)).εIso.inv) =
      (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app (𝟙_ (C E)))
    congr 1
    exact hA.hypothesis11 E
  towerTensor := by
    intro E L M a b X Y
    change ScalarLocalization.composition _ _ _ _ _ _
      (ScalarLocalization.composition _ _ _ _ _ _
        (ScalarLocalization.tensorMap _ _ _
          (1 ⊗ₜ[Integers l Ω M] (A.S.assoc a b).hom.app X.obj)
          (1 ⊗ₜ[Integers l Ω M] (A.S.assoc a b).hom.app Y.obj))
        (1 ⊗ₜ[Integers l Ω M]
          ((A.transitionTensor b).μIso ((A.S.T a).obj X.obj) ((A.S.T a).obj Y.obj)).inv))
      ((rationalTransition A hA b).map
        (1 ⊗ₜ[Integers l Ω L] ((A.transitionTensor a).μIso X.obj Y.obj).inv)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[Integers l Ω M] ((A.transitionTensor (a.trans b)).μIso X.obj Y.obj).inv)
        (1 ⊗ₜ[Integers l Ω M] (A.S.assoc a b).hom.app (X.obj ⊗ Y.obj))
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      ScalarLocalization.tensorMap_tmul, ScalarLocalization.composition_tmul, one_mul]
    congr 1
    exact hA.hypothesis12 a b X.obj Y.obj
  towerUnit := by
    intro E L M a b
    change ScalarLocalization.composition _ _ _ _ _ _
      (1 ⊗ₜ[Integers l Ω M] (A.transitionTensor b).εIso.inv)
      ((rationalTransition A hA b).map
        (1 ⊗ₜ[Integers l Ω L] (A.transitionTensor a).εIso.inv)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[Integers l Ω M] (A.transitionTensor (a.trans b)).εIso.inv)
        (1 ⊗ₜ[Integers l Ω M] (A.S.assoc a b).hom.app (𝟙_ (C E)))
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      ScalarLocalization.composition_tmul, one_mul]
    congr 1
    exact hA.hypothesis13 a b
  scalarTensorSquare := h30
  scalarUnitSquare := h31

  }

/-- The constructed datum satisfies all prescribed rational normalization clauses.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-valid).
Proof: tensor induction gives all localized formulas and the integral identity and
monoidal tower equations. Combine these with the eight scalar normalization equations. -/
theorem rationalDatum_valid : RationalData.Valid C A (rationalDatum A hA) := by
  obtain ⟨h10, h11, h12, h23, h24, h25, h30, h31⟩ := rationalDatum_normalization A hA
  exact rationalDatum_valid_of_equations A hA h10 h11 h12 h23 h24 h25 h30 h31

end WeilConjectures.TensorComparisonDescent
