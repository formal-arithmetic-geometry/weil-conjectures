/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorComparisonEquations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteFirstRootChart
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteRootTensorPresentation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.Orientation.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedSourceChart
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSymmetryCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorShiftCoherence
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorShiftSecond
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorLineChartReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorPullbackCompositionReduction

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: lem-pur-finite-tensor-presentation-reduction)

## Main declarations

- `finiteTensorStructuralCoherence`
- `finiteTensorTau_reduction`
- `finite_tensor_presentation_reduction`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
-- The native derived braiding is a definition, not a global instance.
attribute [local instance] _root_.DerivedCategory.braidedCategory'

namespace WeilConjectures.PurityFiniteSetting

section CupNaturality
set_option backward.defeqAttrib.useBackward true
universe v w
open HomologicalComplex

set_option allowUnsafeReducibility true in
attribute [local reducible] HomologicalComplex.monoidalCategory
  HomologicalComplex.monoidalCategoryStruct CochainComplex.singleFunctor
  CochainComplex.singleFunctors Functor.map₂HomologicalComplex HomologicalComplex.single

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C]

@[irreducible] private def presentation_singleTensorIso (M N : C) :
    (single C (.up ℤ) 0).obj M ⊗ (single C (.up ℤ) 0).obj N ≅
      (single C (.up ℤ) 0).obj (M ⊗ N) :=
  ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) M).app
    ((single C (.up ℤ) 0).obj N)) ≪≫
      ((singleMapHomologicalComplex (tensorLeft M) (.up ℤ) 0).app N)

variable [HasDerivedCategory.{w} C]
  [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]

end CupNaturality

section SingleComparison
section LineFactorization

set_option allowUnsafeReducibility true in
attribute [local reducible] Coefficient coefficientCommRing

attribute [local irreducible] finiteTensorCore finiteTensorLineComparison
  finiteTensorLineMaps finiteTensorFixedLineMap finiteTensorAdjunction
  Adjunction.ofIsRightAdjoint Functor.leftAdjoint Functor.rightAdjoint

end LineFactorization

set_option maxHeartbeats 2000000 in
-- Kernel checking compares the ordinary and derived category presentations in this square.
end SingleComparison

private theorem presentation_chart_reduction
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    (F : C ⥤ D) (s : ℤ)
    (σ : shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s)
    {A U Z : C} {B V Z' : D}
    (u : F.obj U ⟶ V) (b : F.obj A ≅ B) (a : A ≅ U) (a' : B ≅ V)
    (p : Z ≅ A⟦s⟧) (p' : Z' ≅ B⟦s⟧)
    (c : Z ≅ U⟦s⟧) (c' : Z' ≅ V⟦s⟧)
    (hp : p = c ≪≫ (shiftFunctor C s).mapIso a.symm)
    (hp' : p' = c' ≪≫ (shiftFunctor D s).mapIso a'.symm)
    (hc : b.hom ≫ a'.hom = F.map a.hom ≫ u) :
    (F.mapIso p ≪≫ σ.app A ≪≫ (shiftFunctor D s).mapIso b ≪≫ p'.symm).hom ≫
      c'.hom = F.map c.hom ≫ σ.hom.app U ≫ u⟦s⟧' := by
  subst p
  subst p'
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := σ.hom.naturality a.inv
  change F.map (a.inv⟦s⟧') ≫ σ.hom.app A =
    σ.hom.app U ≫ (F.map a.inv)⟦s⟧' at hn
  rw [reassoc_of% hn]
  have hk : F.map a.inv ≫ b.hom ≫ a'.hom = u := by
    rw [hc]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ F.map c.hom ≫ σ.hom.app U ≫ f⟦s⟧') hk

/-- The positive reduction constructed from the signed lines has the prescribed
compatible-root normalization. No level is required to be divisible by ramification.
Source: blueprint proof Step 8
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: lift a primitive root to a compatible infinite root sequence. Its integral
basis reduces to the specified finite root bases, and the balancing map takes
the A basis to the B basis. Recurse on ordered powers and use the same shift signs.
Changing the lift fixes these finite bases. The zero stage is the scalar unit.
The root transition is the indicated power map at every positive quotient level. -/
theorem finiteTensorPositiveReduction_chart (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    (P.finiteTensorPositiveReduction m hm hmn T d).hom ≫
        ((P.finiteReductionSetting m hm).finiteTensorDiagonalChart T d η hη).hom =
      (P.finiteTensorReduction m hm hmn T).map
          (P.finiteTensorDiagonalChart T d ζ hζ).hom ≫
        (P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ))).hom.app _ ≫
        ((P.finiteTensorCore m hm hmn T).εIso.inv)⟦2 * (d : ℤ)⟧' := by
  have hs := (P.existsUnique_finiteTensorPositivePresentation T d).exists.choose_spec ζ hζ
  have ht := ((P.finiteReductionSetting m hm).existsUnique_finiteTensorPositivePresentation
    T d).exists.choose_spec η hη
  have hc := P.finiteTensorLineChart_reduction m hm hmn T d ζ hζ η hη hroot
  have hi := presentation_chart_reduction (P.finiteTensorReduction m hm hmn T)
    (2 * (d : ℤ)) (P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ)))
    (P.finiteTensorCore m hm hmn T).εIso.inv
    (P.finiteTensorLineComparison m hm hmn T d)
    (P.finiteTensorPositiveChart T ζ hζ d)
    ((P.finiteReductionSetting m hm).finiteTensorPositiveChart T η hη d)
    (P.finiteTensorPositivePresentation T d)
    ((P.finiteReductionSetting m hm).finiteTensorPositivePresentation T d)
    (P.finiteTensorDiagonalChart T d ζ hζ)
    ((P.finiteReductionSetting m hm).finiteTensorDiagonalChart T d η hη)
    (eq_of_heq hs) (eq_of_heq ht) hc
  simpa only [finiteTensorPositiveReduction] using hi

/-- The exact inverse second-factor tensor-shift comparison on the actual signed line.
Source: blueprint proof Step 9, Stacks 0FNH
(blueprint: lem-pur-finite-tensor-presentation-reduction). -/
@[irreducible] def finiteTensorTau (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :=
  (((curriedTensor _).obj M).commShiftIso (2 * (d : ℤ))).symm.app
    (P.finiteTensorFixedLine T d)

section TauReduction

attribute [local implicit_reducible] finiteTensorTwist

attribute [local irreducible] finiteTensorTwistShiftComparison
  finiteTensorCore finiteTensorScalarShift finiteTensorLineComparison
  finiteTensorReduction finiteTensorFixedLine finiteTensorFixedSheaf
  Functor.commShiftIso
  _root_.DerivedCategory.commShiftTensorLeft _root_.DerivedCategory.commShift₂CurriedTensor
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

attribute [local irreducible] _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

end TauReduction

section RootChartFinal
universe v w

private theorem chart_unit_core
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (h : F.CoreMonoidal) (M : C) :
    (h.μIso M (𝟙_ C)).inv ≫ F.obj M ◁ h.εIso.inv ≫ (ρ_ (F.obj M)).hom =
      F.map (ρ_ M).hom := by
  let := h.toOplaxMonoidal
  exact Functor.OplaxMonoidal.right_unitality_hom F M

private theorem chart_unit_shift
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (h : F.CoreMonoidal) (s : ℤ)
    (σ : shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s)
    (t : ∀ M : C, shiftFunctor C s ⋙ (curriedTensor C).obj M ≅
      (curriedTensor C).obj M ⋙ shiftFunctor C s)
    (t' : ∀ M : D, shiftFunctor D s ⋙ (curriedTensor D).obj M ≅
      (curriedTensor D).obj M ⋙ shiftFunctor D s)
    (M : C)
    (hs : F.map ((t M).hom.app (𝟙_ C)) ≫ σ.hom.app (M ⊗ (𝟙_ C)) ≫
      ((h.μIso M (𝟙_ C)).inv)⟦s⟧' =
      (h.μIso M ((𝟙_ C)⟦s⟧)).inv ≫ F.obj M ◁ σ.hom.app (𝟙_ C) ≫
        (t' (F.obj M)).hom.app (F.obj (𝟙_ C))) :
    F.map ((t M).hom.app (𝟙_ C) ≫ (ρ_ M).hom⟦s⟧') ≫ σ.hom.app M =
      (h.μIso M ((𝟙_ C)⟦s⟧)).inv ≫
        F.obj M ◁ (σ.hom.app (𝟙_ C) ≫ h.εIso.inv⟦s⟧') ≫
          ((t' (F.obj M)).hom.app (𝟙_ D) ≫ (ρ_ (F.obj M)).hom⟦s⟧') := by
  have hn := (t' (F.obj M)).hom.naturality h.εIso.inv
  change (F.obj M ◁ h.εIso.inv⟦s⟧') ≫ (t' (F.obj M)).hom.app (𝟙_ D) =
    (t' (F.obj M)).hom.app (F.obj (𝟙_ C)) ≫ (F.obj M ◁ h.εIso.inv)⟦s⟧' at hn
  have hu := chart_unit_core F h M
  have hσ := σ.hom.naturality (ρ_ M).hom
  change F.map ((ρ_ M).hom⟦s⟧') ≫ σ.hom.app M =
    σ.hom.app (M ⊗ (𝟙_ C)) ≫ (F.map (ρ_ M).hom)⟦s⟧' at hσ
  simp only [Functor.map_comp, Category.assoc, whiskerLeft_comp]
  rw [reassoc_of% hn, hσ, ← reassoc_of% hs]
  rw [← (shiftFunctor D s).map_comp, ← (shiftFunctor D s).map_comp, hu]

private theorem chart_target_paste
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (h : F.CoreMonoidal) (s : ℤ)
    (σ : shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s)
    (M L : C) (M' L' : D) (p : F.obj M ≅ M') (v : F.obj L ≅ L')
    (a : L ≅ (𝟙_ C)⟦s⟧) (b : L' ≅ (𝟙_ D)⟦s⟧)
    (u : ∀ N : C, N ⊗ (𝟙_ C)⟦s⟧ ≅ N⟦s⟧)
    (u' : ∀ N : D, N ⊗ (𝟙_ D)⟦s⟧ ≅ N⟦s⟧)
    (hv : v.hom ≫ b.hom = F.map a.hom ≫ σ.hom.app (𝟙_ C) ≫ h.εIso.inv⟦s⟧')
    (hu : F.map (u M).hom ≫ σ.hom.app M =
      (h.μIso M ((𝟙_ C)⟦s⟧)).inv ≫
        F.obj M ◁ (σ.hom.app (𝟙_ C) ≫ h.εIso.inv⟦s⟧') ≫ (u' (F.obj M)).hom)
    (hp : p.hom ▷ ((𝟙_ D)⟦s⟧) ≫ (u' M').hom =
      (u' (F.obj M)).hom ≫ p.hom⟦s⟧') :
    ((h.μIso M L).symm ≪≫ tensorIso p v).hom ≫
        (((curriedTensor D).obj M').mapIso b ≪≫ u' M').hom =
      F.map (((curriedTensor C).obj M).mapIso a ≪≫ u M).hom ≫
        σ.hom.app M ≫ p.hom⟦s⟧' := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Functor.mapIso_hom,
    curriedTensor_obj_map, Category.assoc]
  let := h.toOplaxMonoidal
  have hn := Functor.OplaxMonoidal.δ_natural_right F M a.hom
  change (h.μIso M L).inv ≫ F.obj M ◁ F.map a.hom =
    F.map (M ◁ a.hom) ≫ (h.μIso M ((𝟙_ C)⟦s⟧)).inv at hn
  simp only [MonoidalCategory.tensorHom_def', Category.assoc]
  rw [← whisker_exchange_assoc p.hom b.hom, ← whiskerLeft_comp_assoc, hv]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [whiskerLeft_comp, Category.assoc] at hu
  rw [reassoc_of% hn, hp, ← reassoc_of% hu, ← F.map_comp_assoc]

attribute [local irreducible] finiteTensorCore finiteTensorScalarShift
  finiteTensorReduction finiteTensorPositivePresentation finiteTensorLineComparison
  finiteTensorPullbackComparison finiteTensorPuritySourceComparison

private theorem presentation_tensorUnitGeneric_naturality
    (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    {M N : _root_.DerivedCategory C} (a : M ⟶ N) (r : ℤ) :
    ((curriedTensor (_root_.DerivedCategory C)).map a).app
        ((𝟙_ (_root_.DerivedCategory C))⟦r⟧) ≫
      (finiteReductionTensorUnitGeneric C N r).hom =
    (finiteReductionTensorUnitGeneric C M r).hom ≫ a⟦r⟧' := by
  let F := curriedTensor (_root_.DerivedCategory C)
  let := _root_.DerivedCategory.commShiftTensorLeft C M
  let := _root_.DerivedCategory.commShiftTensorLeft C N
  have hs := NatTrans.shift_app_comm (F.map a) r (𝟙_ (_root_.DerivedCategory C))
  dsimp only [finiteReductionTensorUnitGeneric, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, ← hs, Category.assoc, ← (shiftFunctor _ r).map_comp]
  have hn : (F.map a).app (𝟙_ (_root_.DerivedCategory C)) ≫ (ρ_ N).hom =
      (ρ_ M).hom ≫ a := MonoidalCategory.rightUnitor_naturality a
  rw [hn, Functor.map_comp, Category.assoc]

private theorem presentation_tensorUnit_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N) (r : ℤ) :
    ((smoothPurityTensor A X).map a).app
        ((𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))))⟦r⟧) ≫
      (finiteReductionTensorUnit (ModuleCat.{u + 1} A) X N r).hom =
    (finiteReductionTensorUnit (ModuleCat.{u + 1} A) X M r).hom ≫ a⟦r⟧' := by
  have hM := (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} A) X M r).choose_spec.1
  have hN := (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} A) X N r).choose_spec.1
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold finiteReductionTensorUnit
  rw [eM, eN]
  exact presentation_tensorUnitGeneric_naturality _ a r

set_option maxHeartbeats 2000000 in
-- Comparing the native tensor-unit presentations requires extra kernel reduction.
private theorem presentation_tensor_unit_reduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (X : Scheme.{u})
    (M : _root_.DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) (s : ℤ) :
    let F := P.finiteTensorReduction m hm hmn X
    let h := P.finiteTensorCore m hm hmn X
    F.map (finiteReductionTensorUnit (ModuleCat.{u + 1} P.Coefficient) X M s).hom ≫
        (P.finiteTensorScalarShift m hm hmn X s).hom.app M =
      (h.μIso M ((𝟙_ _)⟦s⟧)).inv ≫
        F.obj M ◁ ((P.finiteTensorScalarShift m hm hmn X s).hom.app (𝟙_ _) ≫
          h.εIso.inv⟦s⟧') ≫
        (finiteReductionTensorUnit
          (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) X (F.obj M) s).hom := by
  let F := P.finiteTensorReduction m hm hmn X
  have h := chart_unit_shift F (P.finiteTensorCore m hm hmn X) s
    (P.finiteTensorScalarShift m hm hmn X s)
    (fun N ↦ ((curriedTensor _).obj N).commShiftIso s)
    (fun N ↦ ((curriedTensor _).obj N).commShiftIso s) M
    (P.finiteTensorShiftSecond m hm hmn X M (𝟙_ _) s)
  have heA := eq_of_heq (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} P.Coefficient) X M s).choose_spec.1
  have heB := eq_of_heq (existsUnique_finiteReductionTensorUnit
    (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) X (F.obj M) s).choose_spec.1
  dsimp only [F]
  unfold finiteReductionTensorUnit
  rw [heA, heB]
  exact h

@[irreducible] private def presentation_targetChart (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :=
  ((smoothPurityTensor P.Coefficient X).obj M).mapIso
      (P.finiteTensorDiagonalChart X d ζ hζ) ≪≫
    finiteReductionTensorUnit (ModuleCat.{u + 1} P.Coefficient) X M (2 * (d : ℤ))

private theorem presentation_fixedChart_factor (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReductionFixedChart X d ζ hζ M).hom =
      (P.smoothPurityReassociation X d M).hom ≫
        (presentation_targetChart P X d ζ hζ M).hom := by
  have h := eq_of_heq
    (P.existsUnique_finiteReductionFixedChart X d ζ hζ M).choose_spec.1
  change P.finiteReductionFixedChart X d ζ hζ M = _ at h
  rw [h]
  unfold finiteReductionChartComposite presentation_targetChart
  rfl

private theorem presentation_target_chart_reduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (K : _root_.DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    let F := P.finiteTensorReduction m hm hmn X
    let M := (P.smoothPurityPullback f).obj K
    let M' := ((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
      ((P.finiteTensorReduction m hm hmn Y).obj K)
    (P.finiteTensorPurityTargetComparison m hm hmn f d K).hom ≫
        (presentation_targetChart (P.finiteReductionSetting m hm) X d η hη M').hom =
      F.map (presentation_targetChart P X d ζ hζ M).hom ≫
        (P.finiteTensorScalarShift m hm hmn X (2 * (d : ℤ))).hom.app M ≫
        (P.finiteTensorPullbackComparison m hm hmn f K).hom⟦2 * (d : ℤ)⟧' := by
  let F := P.finiteTensorReduction m hm hmn X
  let M := (P.smoothPurityPullback f).obj K
  let M' := ((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
    ((P.finiteTensorReduction m hm hmn Y).obj K)
  have h := chart_target_paste F (P.finiteTensorCore m hm hmn X) (2 * (d : ℤ))
    (P.finiteTensorScalarShift m hm hmn X (2 * (d : ℤ)))
    M (P.diagonalTwist X d) M' ((P.finiteReductionSetting m hm).diagonalTwist X d)
    (P.finiteTensorPullbackComparison m hm hmn f K)
    (P.finiteTensorPositiveReduction m hm hmn X d)
    (P.finiteTensorDiagonalChart X d ζ hζ)
    ((P.finiteReductionSetting m hm).finiteTensorDiagonalChart X d η hη)
    (fun N ↦ finiteReductionTensorUnit (ModuleCat.{u + 1} P.Coefficient) X N
      (2 * (d : ℤ)))
    (fun N ↦ finiteReductionTensorUnit
      (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) X N (2 * (d : ℤ)))
    (P.finiteTensorPositiveReduction_chart m hm hmn X d ζ η hζ hη hroot)
    (presentation_tensor_unit_reduction P m hm hmn X M (2 * (d : ℤ)))
    (presentation_tensorUnit_naturality _ X
      (P.finiteTensorPullbackComparison m hm hmn f K).hom (2 * (d : ℤ)))
  with_unfolding_all exact h

private theorem presentation_cancel_chart
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B Z : C} {A' B' Z' : D}
    (a : A ⟶ B) (c : B ⟶ Z) (b : A' ⟶ B') (e : B' ≅ Z')
    (c₀ : A ⟶ Z) (c₀' : A' ⟶ Z')
    (s : F.obj A ⟶ A') (t : F.obj B ⟶ B') (w : F.obj Z ⟶ Z')
    (hA : c₀ = a ≫ c) (hB : c₀' = b ≫ e.hom)
    (hs : s ≫ c₀' = F.map c₀ ≫ w)
    (ht : t ≫ e.hom = F.map c ≫ w) : F.map a ≫ t = s ≫ b := by
  rw [hA, hB] at hs
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  rw [ht, ← F.map_comp_assoc, ← hs]

/-- Finite reduction identifies the canonical purity reassociation through precisely
its recorded pullback, tensor, twist and shift comparisons.
Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: choose compatible primitive roots at the two coefficient levels. The
specified source comparison is normalized by the corresponding fixed root charts;
this is transported from its intrinsic normalization through the prescribed
realization units and the shift-compatible scalar presentation. The independent
target comparison is normalized by the diagonal charts: positive line reduction
has precisely that root normalization, and its binary tensor map respects the
second-variable shift and right unitor. Each fixed source chart factors as the
canonical reassociation followed by this target chart. Substitute these two
factorizations in the source normalization, compare with the target normalization,
and cancel the invertible target chart. The argument also covers d=0 and equal
coefficient levels; it requires no coefficient flatness or extra divisibility -/
theorem finite_tensor_presentation_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K)) :
    (P.finiteTensorReduction m hm hmn X).map
        (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj K)).hom ≫
      (P.finiteTensorPurityTargetComparison m hm hmn f d K).hom =
    (P.finiteTensorPuritySourceComparison m hm hmn f d K).hom ≫
      ((P.finiteReductionSetting m hm).smoothPurityReassociation X d
        (((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
          ((P.finiteTensorReduction m hm hmn Y).obj K))).hom := by
  classical
  have _hK := hK
  have hunit : IsUnit (P.diagonalExponent : P.field.k) := by
    simpa only [map_natCast] using
      (P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))).map
        (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨hunit.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let η := ζ ^ (P.coefficients.l ^ (P.level - m))
  have hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent := by
    apply hζ.pow (NeZero.pos P.diagonalExponent)
    change P.coefficients.l ^ P.level =
      P.coefficients.l ^ (P.level - m) * P.coefficients.l ^ m
    rw [← pow_add, Nat.sub_add_cancel hmn]
  let Q := P.finiteReductionSetting m hm
  let F := P.finiteTensorReduction m hm hmn X
  let M := (P.smoothPurityPullback f).obj K
  let M' := (Q.smoothPurityPullback f).obj
    ((P.finiteTensorReduction m hm hmn Y).obj K)
  have hs := P.finiteTensorFixedSourceChart m hm hmn f d K ζ η hζ hη rfl
  have ht := presentation_target_chart_reduction P m hm hmn f d K ζ η hζ hη rfl
  with_unfolding_all exact (presentation_cancel_chart F
    (P.smoothPurityReassociation X d M).hom (presentation_targetChart P X d ζ hζ M).hom
    (Q.smoothPurityReassociation X d M').hom (presentation_targetChart Q X d η hη M')
    (P.finiteReductionFixedChart X d ζ hζ M).hom
    (Q.finiteReductionFixedChart X d η hη M').hom
    (P.finiteTensorPuritySourceComparison m hm hmn f d K).hom
    (P.finiteTensorPurityTargetComparison m hm hmn f d K).hom
    ((P.finiteTensorScalarShift m hm hmn X (2 * (d : ℤ))).hom.app M ≫
      (P.finiteTensorPullbackComparison m hm hmn f K).hom⟦2 * (d : ℤ)⟧')
    (presentation_fixedChart_factor P X d ζ hζ M)
    (presentation_fixedChart_factor Q X d η hη M') hs ht)

end RootChartFinal

end WeilConjectures.PurityFiniteSetting
