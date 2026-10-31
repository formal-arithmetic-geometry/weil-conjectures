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


import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorOrdinaryAddition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSingleProductTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedSourceChart
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSymmetryCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorShiftCoherence
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorShiftSecond
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorLineChartReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorPullbackTensorReduction
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

/-- Scalar extension respects the native symmetry and simultaneous shift comparison.
Associativity and unit equations are fields of finiteTensorCore.
Source: blueprint proof Steps 2 and 6, Stacks 0FPT and 0FNH
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: on flat-term K-flat representatives the binary map distributes the quotient
scalar into the first tensor factor. Both symmetry routes multiply the same scalars
and carry the same Koszul sign. The shift routes agree degreewise since the ring
map preserves -1. Descend through K-flat localization; the native shift comparison
is defined by the same localization, for all integer shifts. -/
theorem finiteTensorStructuralCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (∀ U V, FiniteTensorSymmetrySquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorCore m hm hmn T) U V) ∧
    ∀ U V (a b : ℤ), FiniteTensorShiftSquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorScalarShift m hm hmn T)
      (P.finiteTensorCore m hm hmn T) U V a b
      (_root_.DerivedCategory.shiftTensorShiftIso _ U V a b)
      (_root_.DerivedCategory.shiftTensorShiftIso _
        ((P.finiteTensorReduction m hm hmn T).obj U)
        ((P.finiteTensorReduction m hm hmn T).obj V) a b) := by
  constructor
  · intro U V
    exact P.finiteTensorSymmetryCoherence m hm hmn T U V
  · intro U V a b
    exact P.finiteTensorShiftCoherence m hm hmn T U V a b

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

private theorem presentation_singleTensorIso_inv_f (M N : C) :
    (presentation_singleTensorIso M N).inv.f 0 =
      ιTensorObj ((single C (.up ℤ) 0).obj M)
        ((single C (.up ℤ) 0).obj N) 0 0 0 rfl := by
  unfold presentation_singleTensorIso
  simp only [Iso.trans_inv, Iso.app_inv, comp_f,
    CochainComplex.map₂HomologicalComplexObjSingleIso_inv_app,
    singleMapHomologicalComplex_inv_app_self, CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  dsimp only [singleObjXSelf, singleObjXIsoOfEq, HomologicalComplex.single,
    tensorLeft, curriedTensor, eqToIso]
  simp only [eqToHom_refl, whiskerLeft_id, id_whiskerRight, Category.id_comp]
  with_unfolding_all exact Category.id_comp _

@[reassoc] private theorem presentation_singleTensorIso_naturality
    {M N M' N' : C} (f : M ⟶ M') (g : N ⟶ N') :
    ((single C (.up ℤ) 0).map f ⊗ₘ (single C (.up ℤ) 0).map g) ≫
        (presentation_singleTensorIso M' N').hom =
      (presentation_singleTensorIso M N).hom ≫ (single C (.up ℤ) 0).map (f ⊗ₘ g) := by
  apply (cancel_epi (presentation_singleTensorIso M N).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (presentation_singleTensorIso M' N').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  simp only [comp_f, presentation_singleTensorIso_inv_f]
  simp only [MonoidalCategory.tensorHom_def, comp_f]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f]
  simp [Category.assoc]

variable [HasDerivedCategory.{w} C]
  [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]

@[reassoc] private theorem presentation_cup_naturality
    {M N M' N' : C} (f : M ⟶ M') (g : N ⟶ N') :
    ((DerivedCategory.singleFunctor C 0).map f ⊗ₘ
      (DerivedCategory.singleFunctor C 0).map g) ≫
        AlgebraicGeometry.ProEtale.cupSingleTensorMap M' N' =
      AlgebraicGeometry.ProEtale.cupSingleTensorMap M N ≫
        (DerivedCategory.singleFunctor C 0).map (f ⊗ₘ g) := by
  have hf := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality f
  have hg := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality g
  have hi := (DerivedCategory.singleFunctorIsoCompQ C 0).inv.naturality (f ⊗ₘ g)
  dsimp only [Functor.comp_map, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors] at hf hg hi
  simp only [AlgebraicGeometry.ProEtale.cupSingleTensorMap, tensorIso_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  have fac (A B : C) : (presentation_singleTensorIso A B).hom =
      (((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) A).app
          ((single C (.up ℤ) 0).obj B)) ≪≫
        ((singleMapHomologicalComplex (tensorLeft A) (.up ℤ) 0).app B)).hom := by
    unfold presentation_singleTensorIso
    rfl
  rw [← fac, ← fac]
  erw [tensorHom_comp_tensorHom_assoc, hf, hg,
    ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc,
    ← DerivedCategory.Q.map_comp_assoc, presentation_singleTensorIso_naturality,
    DerivedCategory.Q.map_comp, Category.assoc, hi]

end CupNaturality

private theorem presentation_single_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (R : D ⥤ C) (Q : E ⥤ F) (V : F ⥤ E)
    (i : C ⥤ E) (j : D ⥤ F) (a : S ⊣ R) (b : Q ⊣ V)
    (k : j ⋙ V ≅ R ⋙ i) {M N : C} (f : M ⟶ N) :
    Q.map (i.map f) ≫ purityAdjunctionSingleMap S R Q V i j a b k N =
      purityAdjunctionSingleMap S R Q V i j a b k M ≫ j.map (S.map f) := by
  unfold purityAdjunctionSingleMap
  rw [← b.homEquiv_naturality_left_symm, ← b.homEquiv_naturality_right_symm]
  congr 1
  rw [← i.map_comp_assoc, ← a.unit_naturality f, i.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (i.map (a.unit.app M) ≫ ·) (k.inv.naturality (S.map f))

private theorem presentation_product_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    (S : C ⥤ D) (Q : E ⥤ F) (i : C ⥤ E) (j : D ⥤ F)
    (s : ∀ M, Q.obj (i.obj M) ⟶ j.obj (S.obj M))
    (hs : ∀ {M N} (f : M ⟶ N), Q.map (i.map f) ≫ s N = s M ≫ j.map (S.map f))
    (v : ∀ M N, i.obj M ⊗ i.obj N ⟶ i.obj (M ⊗ N))
    (w : ∀ M N, j.obj M ⊗ j.obj N ⟶ j.obj (M ⊗ N))
    (hw : ∀ {M N M' N'} (a : M ⟶ M') (b : N ⟶ N'),
      (j.map a ⊗ₘ j.map b) ≫ w M' N' = w M N ≫ j.map (a ⊗ₘ b))
    (M N W : C) (M' N' W' : D) (p : M ⊗ N ⟶ W) (q : M' ⊗ N' ⟶ W')
    (a : S.obj M ⟶ M') (b : S.obj N ⟶ N') (c : S.obj W ⟶ W')
    (d : S.obj (M ⊗ N) ⟶ S.obj M ⊗ S.obj N)
    (e : Q.obj (i.obj M ⊗ i.obj N) ⟶ Q.obj (i.obj M) ⊗ Q.obj (i.obj N))
    (hpq : S.map p ≫ c = d ≫ (a ⊗ₘ b) ≫ q)
    (hb : Q.map (v M N) ≫ s (M ⊗ N) ≫ j.map d = e ≫ (s M ⊗ₘ s N) ≫ w (S.obj M) (S.obj N)) :
    Q.map (v M N ≫ i.map p) ≫ (s W ≫ j.map c) =
      e ≫ ((s M ≫ j.map a) ⊗ₘ (s N ≫ j.map b)) ≫ w M' N' ≫ j.map q := by
  calc
    Q.map (v M N ≫ i.map p) ≫ (s W ≫ j.map c) =
        (Q.map (v M N) ≫ s (M ⊗ N)) ≫ j.map (S.map p ≫ c) := by
      rw [Q.map_comp, j.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% (hs p)]
    _ = (Q.map (v M N) ≫ s (M ⊗ N)) ≫ j.map (d ≫ (a ⊗ₘ b) ≫ q) := by rw [hpq]
    _ = (Q.map (v M N) ≫ s (M ⊗ N) ≫ j.map d) ≫ j.map (a ⊗ₘ b) ≫ j.map q := by
      simp only [j.map_comp, Category.assoc]
    _ = (e ≫ (s M ⊗ₘ s N) ≫ w (S.obj M) (S.obj N)) ≫
        j.map (a ⊗ₘ b) ≫ j.map q := by rw [hb]
    _ = e ≫ ((s M ≫ j.map a) ⊗ₘ (s N ≫ j.map b)) ≫ w M' N' ≫ j.map q := by
      simp only [Category.assoc]
      rw [← reassoc_of% (hw a b), tensorHom_comp_tensorHom_assoc]

section SingleComparison
section LineFactorization

set_option allowUnsafeReducibility true in
attribute [local reducible] Coefficient coefficientCommRing

attribute [local irreducible] finiteTensorCore finiteTensorLineComparison
  finiteTensorLineMaps finiteTensorFixedLineMap finiteTensorAdjunction
  Adjunction.ofIsRightAdjoint Functor.leftAdjoint Functor.rightAdjoint

private theorem presentation_single_factor
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (R : D ⥤ C) (Q : E ⥤ F) (V : F ⥤ E)
    (i : C ⥤ E) (j : D ⥤ F) (a : S ⊣ R) (b : Q ⊣ V)
    (k : j ⋙ V ≅ R ⋙ i) (M : C) (N : D) (g : S.obj M ⟶ N) :
    purityAdjunctionSingleMap S R Q V i j a b k M ≫ j.map g =
      (b.homEquiv _ _).symm (i.map (a.homEquiv _ _ g) ≫ k.inv.app N) := by
  unfold purityAdjunctionSingleMap
  rw [← b.homEquiv_naturality_right_symm]
  congr 1
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (i.map (a.unit.app M) ≫ ·) (k.inv.naturality g).symm

private theorem presentation_line_factor (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r : ℤ) :
    let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
    let E := ProEtale.sheafExtendScalars φ T
    let U := sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)
    let F := P.finiteTensorReduction m hm hmn T
    let G := ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
      (P.finiteReductionRingHom m hm hmn) T
    let i := DerivedCategory.singleFunctor.{u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0
    let j := DerivedCategory.singleFunctor.{u + 1}
      (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)) 0
    let a : E ⊣ U := ProEtale.sheafExtendScalarsAdjunction φ T
    let b : F ⊣ G := P.finiteTensorAdjunction m hm hmn T
    let M := P.finiteTensorFixedSheaf T r
    let N := (P.finiteReductionSetting m hm).finiteTensorFixedSheaf T r
    let c := P.finiteTensorFixedLineMap m hm hmn T
      (P.finiteTensorLineMaps m hm hmn T) r
    (P.finiteTensorLineComparison m hm hmn T r).hom =
      purityAdjunctionSingleMap E U F G i j a b
        (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1} U 0) M ≫
        j.map ((a.homEquiv M N).symm c) := by
  dsimp only
  let φ := P.finiteReductionRingHom m hm hmn
  let Q := P.finiteReductionSetting m hm
  let M := P.finiteTensorFixedSheaf T r
  let N := Q.finiteTensorFixedSheaf T r
  let E := ProEtale.sheafExtendScalars φ.ulift.{u + 1, u + 1} T
  let U := sfFixedRestriction.{u, u + 1, u + 1} T φ
  let F := P.finiteTensorReduction m hm hmn T
  let G := ProEtale.SupportedEtaleTensorOrigin.fixedRestriction φ T
  let adj : E ⊣ U := ProEtale.sheafExtendScalarsAdjunction φ.ulift.{u + 1, u + 1} T
  let ad : F ⊣ G := P.finiteTensorAdjunction m hm hmn T
  let f : M ⟶ U.obj N := P.finiteTensorFixedLineMap m hm hmn T
    (P.finiteTensorLineMaps m hm hmn T) r
  let d : E.obj M ⟶ N := (adj.homEquiv M N).symm f
  let i := DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0
  let j := DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q.Coefficient)) 0
  let s := purityAdjunctionSingleMap E U F G i j
    adj ad (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1} U 0) M
  have he : s ≫ j.map d = (ad.homEquiv _ _).symm
      (i.map f ≫ (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1} U 0).inv.app N) := by
    have hdf : adj.homEquiv M N d = f := (adj.homEquiv M N).apply_symm_apply f
    exact (presentation_single_factor E U F G i j adj ad
      (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1} U 0) M N d).trans
        (congrArg (fun t : M ⟶ U.obj N ↦
          (ad.homEquiv (i.obj M) (j.obj N)).symm
            (i.map t ≫ (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1} U 0).inv.app N)) hdf)
  apply Eq.trans _ he.symm
  apply (Equiv.eq_symm_apply (ad.homEquiv _ _)).2
  have h := (P.existsUnique_finiteTensorLines m hm hmn T).choose_spec.1.2.choose_spec.1 r
  unfold TransposedFamilyData.Pointwise finiteTensorLineComparisonData at h
  simp only [ad, i, f, U, N, Q, G, φ, finiteTensorLineComparison, finiteTensorLineMaps,
    finiteTensorFixedSheaf, finiteTensorFixedLine, Coefficient] at h ⊢
  with_unfolding_all exact eq_of_heq h


end LineFactorization

private theorem presentation_product_hom (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    (P.finiteTensorProduct T r t).hom =
      ProEtale.cupSingleTensorMap
        (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t) ≫
      (DerivedCategory.singleFunctor _ 0).map (P.finiteTensorSheafProducts T r t).hom := by
  exact eq_of_heq (P.existsUnique_finiteTensorProducts T r t).exists.choose_spec

set_option maxHeartbeats 2000000 in
-- Kernel checking compares the ordinary and derived category presentations in this square.
/-- Signed addition commutes with the normalized reduction of the actual lines.
Source: blueprint proof Step 5
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: finiteTensorOrdinaryAddition supplies the ordinary product square for the
adjuncts of the normalized signed-line maps. finiteTensorSingleProductTransport
supplies the binary square for the canonical scalar/single maps. Their naturality
and naturality of cupSingleTensorMap assemble these two squares. The adjunction
hom equivalences identify scalar/single followed by each ordinary adjunct with the
chosen derived line comparison. Product normalization identifies each derived
product with the cup map followed by the single of the ordinary product. Rewriting
these normalizations gives the displayed equation. -/
theorem finiteTensorTwistAdditionCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    (P.finiteTensorReduction m hm hmn T).map (P.finiteTensorProduct T r t).hom ≫
        (P.finiteTensorLineComparison m hm hmn T (r + t)).hom =
      ((P.finiteTensorCore m hm hmn T).μIso
        (P.finiteTensorFixedLine T r) (P.finiteTensorFixedLine T t)).inv ≫
        ((P.finiteTensorLineComparison m hm hmn T r).hom ⊗ₘ
          (P.finiteTensorLineComparison m hm hmn T t).hom) ≫
        ((P.finiteReductionSetting m hm).finiteTensorProduct T r t).hom := by
  let Q := P.finiteReductionSetting m hm
  let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
  let E := ProEtale.sheafExtendScalars φ T
  let U := sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)
  let F := P.finiteTensorReduction m hm hmn T
  let G := ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
    (P.finiteReductionRingHom m hm hmn) T
  let i := DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0
  let j := DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q.Coefficient)) 0
  let a : E ⊣ U := ProEtale.sheafExtendScalarsAdjunction φ T
  let b : F ⊣ G := P.finiteTensorAdjunction m hm hmn T
  let k := Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1} U 0
  let s := purityAdjunctionSingleMap E U F G i j a b k
  let c := P.finiteTensorLineMaps m hm hmn T
  let d := fun l : ℤ ↦ (a.homEquiv _ _).symm
    (P.finiteTensorFixedLineMap m hm hmn T c l)
  have hp := P.finiteTensorOrdinaryAddition m hm hmn T r t
  have hb := P.finiteTensorSingleProductTransport m hm hmn T
    (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)
  have h := presentation_product_transport E F i j s
    (fun f ↦ presentation_single_naturality E U F G i j a b k f)
    (ProEtale.cupSingleTensorMap (hD := ProEtale.cupHasDerivedCategory P T))
    (ProEtale.cupSingleTensorMap (hD := ProEtale.cupHasDerivedCategory Q T))
    (fun a b ↦ presentation_cup_naturality a b)
    (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)
    (P.finiteTensorFixedSheaf T (r + t))
    (Q.finiteTensorFixedSheaf T r) (Q.finiteTensorFixedSheaf T t)
    (Q.finiteTensorFixedSheaf T (r + t))
    (P.finiteTensorSheafProducts T r t).hom
    (Q.finiteTensorSheafProducts T r t).hom (d r) (d t) (d (r + t))
    (Functor.OplaxMonoidal.δ E _ _)
    ((P.finiteTensorCore m hm hmn T).μIso
      (P.finiteTensorFixedLine T r) (P.finiteTensorFixedLine T t)).inv hp hb
  rw [presentation_product_hom P T r t, presentation_product_hom Q T r t,
    presentation_line_factor P m hm hmn T (r + t),
    presentation_line_factor P m hm hmn T r,
    presentation_line_factor P m hm hmn T t]
  simp only [Q, φ, E, U, F, G, i, j, a, b, k, s, c, d,
    finiteTensorFixedLine, finiteTensorFixedSheaf] at h ⊢
  exact h


end SingleComparison

/-- The recorded scalar mate respects tensor pullback and the exact-derived compositor.
Source: blueprint proof Step 7; Stacks 07A4
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: on K-flat cochains both pullback/scalar routes send a pulled-back section
tensor b to its inverse image tensor b. The ordinary tensor and composition
constraints are those of inverse image, and both composites use the same scalar
unit. Their representative equations descend through localization. The displayed
maps are exactly those adjuncts by the realization unit and counit identities. -/
theorem finiteTensorPullbackCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (∀ K L,
      (P.finiteTensorReduction m hm hmn X).map
          (P.finiteTensorPullbackTensor f K L).hom ≫
        ((P.finiteTensorCore m hm hmn X).μIso
          ((P.smoothPurityPullback f).obj K) ((P.smoothPurityPullback f).obj L)).inv ≫
        ((P.finiteTensorPullbackComparison m hm hmn f K).hom ⊗ₘ
          (P.finiteTensorPullbackComparison m hm hmn f L).hom) =
      (P.finiteTensorPullbackComparison m hm hmn f (K ⊗ L)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          ((P.finiteTensorCore m hm hmn Y).μIso K L).inv ≫
        ((P.finiteReductionSetting m hm).finiteTensorPullbackTensor f
          ((P.finiteTensorReduction m hm hmn Y).obj K)
          ((P.finiteTensorReduction m hm hmn Y).obj L)).hom) ∧
    ∀ K,
      (P.finiteTensorReduction m hm hmn X).map
          ((compositionFixedPullbackComp P.Ring f g).hom.app K) ≫
        (P.finiteTensorPullbackComparison m hm hmn f ((P.smoothPurityPullback g).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          (P.finiteTensorPullbackComparison m hm hmn g K).hom =
      (P.finiteTensorPullbackComparison m hm hmn (f ≫ g) K).hom ≫
        (compositionFixedPullbackComp (P.finiteReductionSetting m hm).Ring f g).hom.app
          ((P.finiteTensorReduction m hm hmn Z).obj K) := by
  constructor
  · exact P.finiteTensorPullbackTensorReduction m hm hmn f
  · exact P.finiteTensorPullbackCompositionReduction m hm hmn f g

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

private theorem direct_two_squares
    {C : Type*} [Category* C] {A B U V U' V' : C}
    (a : B ≅ A) (t : U ≅ V) (b : V' ≅ U')
    (x : A ⟶ U) (y : B ⟶ V) (u : U ⟶ U') (v : V ⟶ V')
    (z : A ⟶ U') (e : B ⟶ V')
    (ha : a.inv ≫ y = x ≫ t.hom)
    (hb : u ≫ b.inv = t.hom ≫ v)
    (hz : z = x ≫ u) (he : e = y ≫ v) :
    a.hom ≫ z = e ≫ b.hom := by
  rw [hz, he]
  apply (cancel_epi a.inv).1
  apply (cancel_mono b.inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% ha, hb]

private theorem tensor_composite_factor
    {C : Type*} [Category* C] [MonoidalCategory C]
    {Q U V Z : C} (W : C) (δ : Q ⟶ W ⊗ U) (f : U ⟶ V) (g : V ⟶ Z) :
    δ ≫ (𝟙 W ⊗ₘ (f ≫ g)) = (δ ≫ W ◁ f) ≫ W ◁ g := by
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]

private theorem tensor_shift_component_hom
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (h : F.CoreMonoidal) (s : ℤ)
    (σ : shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s)
    (M A : C) (B : D) (b : F.obj A ≅ B) :
    (finiteTensorTwistShiftComponent F h M A B b s (σ.app (M ⊗ A))).hom =
      (σ.hom.app (M ⊗ A) ≫ ((h.μIso M A).inv)⟦s⟧') ≫
        (F.obj M ◁ b.hom)⟦s⟧' := by
  simp only [finiteTensorTwistShiftComponent, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Functor.map_comp,
    id_tensorHom, Category.assoc]

private theorem tau_component (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :
    (P.finiteTensorTwistShiftComparison m hm hmn T d (2 * (d : ℤ))).hom.app M =
      (finiteTensorTwistShiftComponent (P.finiteTensorReduction m hm hmn T)
        (P.finiteTensorCore m hm hmn T) M (P.finiteTensorFixedLine T d)
        ((P.finiteReductionSetting m hm).finiteTensorFixedLine T d)
        (P.finiteTensorLineComparison m hm hmn T d) (2 * (d : ℤ))
        ((P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ))).app
          (M ⊗ P.finiteTensorFixedLine T d))).hom := by
  unfold finiteTensorTwistShiftComparison
  exact congrArg Iso.hom (eq_of_heq ((P.existsUnique_finiteTensorTwistShiftComparison
    m hm hmn T d (2 * (d : ℤ))).exists.choose_spec M))

private theorem tau_second_square (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :
    let F := P.finiteTensorReduction m hm hmn T
    let s : ℤ := 2 * (d : ℤ)
    let A := P.finiteTensorFixedLine T d
    let σ := P.finiteTensorScalarShift m hm hmn T s
    let δ (X Y) := ((P.finiteTensorCore m hm hmn T).μIso X Y).inv
    let tB := ((curriedTensor _).obj (F.obj M)).commShiftIso s
    (F.mapIso (P.finiteTensorTau T M d).symm).hom ≫
        (σ.hom.app (M ⊗ A) ≫ (δ M A)⟦s⟧') =
      (δ M (A⟦s⟧) ≫ F.obj M ◁ σ.hom.app A) ≫ (tB.app (F.obj A)).hom := by
  simpa only [Functor.mapIso_hom, Iso.symm_hom, finiteTensorTau,
    Iso.app_inv, Iso.symm_inv, Iso.app_hom, Category.assoc] using
    P.finiteTensorShiftSecond m hm hmn T M (P.finiteTensorFixedLine T d) (2 * (d : ℤ))

private theorem tau_line_square (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :
    let F := P.finiteTensorReduction m hm hmn T
    let s : ℤ := 2 * (d : ℤ)
    let A := P.finiteTensorFixedLine T d
    let b := P.finiteTensorLineComparison m hm hmn T d
    let tB := ((curriedTensor _).obj (F.obj M)).commShiftIso s
    F.obj M ◁ b.hom⟦s⟧' ≫
        ((P.finiteReductionSetting m hm).finiteTensorTau T (F.obj M) d).symm.hom =
      (tB.app (F.obj A)).hom ≫ (F.obj M ◁ b.hom)⟦s⟧' := by
  simpa only [finiteTensorTau, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.comp_map, curriedTensor_obj_map] using
    ((((curriedTensor _).obj ((P.finiteTensorReduction m hm hmn T).obj M)).commShiftIso
      (2 * (d : ℤ))).hom.naturality (P.finiteTensorLineComparison m hm hmn T d).hom)

/-- Reduction commutes with this precise reassociation of every signed-line presentation.
Source: blueprint proof Steps 6 and 9, Stacks 07A4 and 0FNH
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: the native second-factor shift acts on a homogeneous tensor with the sign
(-1)^(2dp). Scalar reduction preserves that sign and the normalized binary map.
Apply the shift equation and then naturality in the line map. This proves the
square before localization on all K-flat representatives, hence in the derived category. -/
theorem finiteTensorTau_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :
    (P.finiteTensorReduction m hm hmn T).map (P.finiteTensorTau T M d).hom ≫
      ((P.finiteTensorCore m hm hmn T).μIso M
        ((P.finiteTensorFixedLine T d)⟦2 * (d : ℤ)⟧)).inv ≫
      (𝟙 _ ⊗ₘ
        ((P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ))).hom.app
            (P.finiteTensorFixedLine T d) ≫
          ((P.finiteTensorLineComparison m hm hmn T d).hom)⟦2 * (d : ℤ)⟧')) =
    (P.finiteTensorTwistShiftComparison m hm hmn T d (2 * (d : ℤ))).hom.app M ≫
      ((P.finiteReductionSetting m hm).finiteTensorTau T
        ((P.finiteTensorReduction m hm hmn T).obj M) d).hom := by
  have he' := tau_component P m hm hmn T M d
  refine Eq.trans ?_ (congrArg (fun a ↦ a ≫
    ((P.finiteReductionSetting m hm).finiteTensorTau T
      ((P.finiteTensorReduction m hm hmn T).obj M) d).hom) he').symm
  let F := P.finiteTensorReduction m hm hmn T
  let s : ℤ := 2 * (d : ℤ)
  let A := P.finiteTensorFixedLine T d
  let B := (P.finiteReductionSetting m hm).finiteTensorFixedLine T d
  let σ := P.finiteTensorScalarShift m hm hmn T s
  let δ (X Y) := ((P.finiteTensorCore m hm hmn T).μIso X Y).inv
  let b := P.finiteTensorLineComparison m hm hmn T d
  let tB := ((curriedTensor _).obj (F.obj M)).commShiftIso s
  have hs := tau_second_square P m hm hmn T M d
  have hn := tau_line_square P m hm hmn T M d
  have h := direct_two_squares (F.mapIso (P.finiteTensorTau T M d))
    (tB.app (F.obj A))
    ((P.finiteReductionSetting m hm).finiteTensorTau T (F.obj M) d)
    (δ M (A⟦s⟧) ≫ F.obj M ◁ σ.hom.app A)
    (σ.hom.app (M ⊗ A) ≫ (δ M A)⟦s⟧')
    (F.obj M ◁ b.hom⟦s⟧') ((F.obj M ◁ b.hom)⟦s⟧')
    (δ M (A⟦s⟧) ≫ (𝟙 _ ⊗ₘ (σ.hom.app A ≫ b.hom⟦s⟧')))
    (finiteTensorTwistShiftComponent F (P.finiteTensorCore m hm hmn T) M A B b s
      (σ.app (M ⊗ A))).hom hs hn
    (tensor_composite_factor (F.obj M) (δ M (A⟦s⟧)) (σ.hom.app A) (b.hom⟦s⟧'))
    (tensor_shift_component_hom F (P.finiteTensorCore m hm hmn T) s σ M A B b)
  simpa only [F, s, A, B, σ, δ, b, Functor.comp_obj, curriedTensor_obj_obj,
    Functor.mapIso_hom, Iso.symm_inv] using h


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
