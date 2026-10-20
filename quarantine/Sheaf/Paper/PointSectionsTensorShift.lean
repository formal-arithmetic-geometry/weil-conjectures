/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.Paper.PointSectionsScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # The canonical sections-tensor comparison commutes with shifts

Source: Stacks Project, Tag 03EK, sectionwise tensor and sheafification; blueprint
`def-weil-finite-coefficient-point`, final-display argument
(blueprint: lem-weil-point-sections-tensor-shift).

The comparison itself is the existing `pointDerivedSectionsTensor`. The shift on
ordinary derived scalar extension is transported from exact termwise scalar extension
through its canonical, representative-normalized comparison, independently of theta.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures

variable (k : Type u) [Field k] [IsAlgClosed k]
  (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The standard termwise shift on ordinary derived tensor at the point. Its zero and
addition laws are those of `Functor.CommShift.ofIso`; the isomorphism used here is fixed
on every complex by the universal change-of-rings counit, not by theta.
Source: Stacks 06YY and the blueprint final-display argument
(blueprint: lem-weil-point-sections-tensor-shift). -/
instance pointCompletedScalarCommShift :
    (completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k))).CommShift ℤ :=
  Functor.CommShift.ofIso (pointOrdinaryDerivedComparison k l E L ι).symm ℤ

/-- The source of the existing termwise sections-tensor comparison.
Source: Stacks 03EK (blueprint: lem-weil-point-sections-tensor-shift). -/
abbrev pointSectionsTensorSource :=
  pointCompletedSections k l E ⋙ pointIntegralModuleTensor l E L ι

/-- The target of the existing termwise sections-tensor comparison.
Source: Stacks 03EK (blueprint: lem-weil-point-sections-tensor-shift). -/
abbrev pointSectionsTensorTarget :=
  completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
    pointCompletedSections k l L

/-- The existing comparison applied termwise, hence a natural map of complexes.
Source: Stacks 03EK (blueprint: lem-weil-point-sections-tensor-shift). -/
def pointSectionsTensorComplex :=
  NatIso.mapHomologicalComplex (pointSectionsTensor k l E L ι) (ComplexShape.up ℤ)

/-- The source of the existing derived sections-tensor comparison.
Source: blueprint final display (blueprint: lem-weil-point-sections-tensor-shift). -/
abbrev pointSectionsTensorDerivedSource :=
  pointCompletedDerivedSections k l E ⋙ pointIntegralModuleDerivedTensor l E L ι

/-- The target uses ordinary derived change of rings, before completion.
Source: Stacks 06YY (blueprint: lem-weil-point-sections-tensor-shift). -/
abbrev pointSectionsTensorDerivedTarget :=
  completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
    pointCompletedDerivedSections k l L

/-- The canonical source identification on a complex representative.
Source: exact termwise sections and tensor, blueprint final-display argument
(blueprint: lem-weil-point-sections-tensor-shift). -/
def pointSectionsTensorSourceFactors :
    DerivedCategory.Q ⋙ pointSectionsTensorDerivedSource k l E L ι ≅
      (pointSectionsTensorSource k l E L ι).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.mapDerivedCategoryCompIso
        (pointCompletedSections k l E) (pointIntegralModuleTensor l E L ι)).symm ≪≫
    (pointSectionsTensorSource k l E L ι).mapDerivedCategoryFactors

/-- The canonical target identification on a complex representative. This uses the
ordinary derived-tensor counit normalization and exact termwise sections.
Source: Stacks 06YY, blueprint final-display argument
(blueprint: lem-weil-point-sections-tensor-shift). -/
def pointSectionsTensorTargetFactors :
    DerivedCategory.Q ⋙ pointSectionsTensorDerivedTarget k l E L ι ≅
      (pointSectionsTensorTarget k l E L ι).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι)
          (pointCompletedDerivedSections k l L) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
          (pointCompletedSections k l L)).symm) ≪≫
    (pointSectionsTensorTarget k l E L ι).mapDerivedCategoryFactors

/-- The canonical sections-tensor map commutes with every integer shift and is computed
by its balanced degreewise formula on every K-flat, flat-term representative.
Source: Stacks 03EK (tensor construction); the final-display argument of blueprint
`def-weil-finite-coefficient-point`
(blueprint: lem-weil-point-sections-tensor-shift).

Proof:
1. Choose a degreewise epimorphic K-flat resolution with flat terms using
   lem-pc-kflat-resolution. The ordinary tensor complex computes derived change of
   rings by lem-pur-derived-change-of-rings. The comparison of
   lem-weil-point-sections-scalar-extension sends b tensor a to the sheafified section
   b_s tensor a, using def-pur-sheaf-tensor-product. Balancing and compatibility with
   restrictions make this a module map, and compatibility with differentials makes
   its termwise extension a chain map, naturally in complexes.
2. In degree r of P[m] the formula is the degree r+m formula for P. The coefficient
   b_s has degree zero; both differentials acquire the same shift sign. This gives
   the chain-level square below. Zero shifts act identically, and successive shifts
   reindex twice, giving the zero and addition laws of the standard CommShift structures.
3. Exact sections (lem-weil-point-proetale-sections-exact) and finite-free coefficient
   tensor preserve quasi-isomorphisms. The universal derived-tensor counit identifies
   each K-flat computation with the same derived functor. Two resolutions admit a
   common K-flat refinement of their fibre product over the original complex: its
   projections are quasi-isomorphisms since their kernels are acyclic. Naturality
   makes their comparison squares commute. Inverting quasi-isomorphisms in roofs
   descends both the representative formula and its shift square. Thus the last
   equality holds for every representative isomorphism e and is independent of its
   resolution, and the first square holds in D(O_L). -/
theorem pointSectionsTensorShift
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Qbar : Type u) [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (E L : IntermediateField ℚ_[l] Qbar)
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (hEL : E ≤ L)
    (K : (sfIntegralConstructible l E (Spec (.of D.k))).FullSubcategory) :
    (∀ m : ℤ,
      ((pointSectionsTensorDerivedSource D.k l E L (IntermediateField.inclusion hEL)).commShiftIso
          m).hom.app K.obj ≫ ((pointDerivedSectionsTensor D.k l E L
            (IntermediateField.inclusion hEL)).hom.app K.obj)⟦m⟧' =
        (pointDerivedSectionsTensor D.k l E L
            (IntermediateField.inclusion hEL)).hom.app (K.obj⟦m⟧) ≫
          ((pointSectionsTensorDerivedTarget D.k l E L
            (IntermediateField.inclusion hEL)).commShiftIso m).hom.app K.obj) ∧
    (∀ (P : CochainComplex (integralTowerModules.{u, u} l E (Spec (.of D.k))) ℤ)
      (_hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (Scheme.ProEt (Spec (.of D.k))) inferInstance (essentiallySmallSelf.{0} _)
        (Scheme.ProEt.topology (Spec (.of D.k)))
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of D.k))) P)
      (_hflat : ∀ r : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology (Spec (.of D.k)))
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of D.k))) (P.X r))
      (e : DerivedCategory.Q.obj P ≅ K.obj),
      (∀ (r : ℤ) (b : Padic.coefficientExtensionIntegers l L)
        (a : (pointCompletedSections D.k l E).obj (P.X r)),
        (((pointSectionsTensorComplex D.k l E L
          (IntermediateField.inclusion hEL)).hom.app P).f r)
            (b ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L (IntermediateField.inclusion hEL)] a) =
          completedScalarTensorSection.{u, u} l E L (IntermediateField.inclusion hEL)
            (Spec (.of D.k)) (P.X r) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
            (pointCompletedConstant D.k l L b) a) ∧
      (∀ m : ℤ,
        ((pointSectionsTensorSource D.k l E L
          (IntermediateField.inclusion hEL)).mapCochainComplexShiftIso m).hom.app P ≫
            ((pointSectionsTensorComplex D.k l E L
              (IntermediateField.inclusion hEL)).hom.app P)⟦m⟧' =
          (pointSectionsTensorComplex D.k l E L
              (IntermediateField.inclusion hEL)).hom.app (P⟦m⟧) ≫
            ((pointSectionsTensorTarget D.k l E L
              (IntermediateField.inclusion hEL)).mapCochainComplexShiftIso m).hom.app P) ∧
      (pointSectionsTensorDerivedSource D.k l E L
          (IntermediateField.inclusion hEL)).map e.hom ≫
        (pointDerivedSectionsTensor D.k l E L
          (IntermediateField.inclusion hEL)).hom.app K.obj ≫
        (pointSectionsTensorDerivedTarget D.k l E L
          (IntermediateField.inclusion hEL)).map e.inv ≫
        (pointSectionsTensorTargetFactors D.k l E L
          (IntermediateField.inclusion hEL)).hom.app P =
          (pointSectionsTensorSourceFactors D.k l E L
              (IntermediateField.inclusion hEL)).hom.app P ≫
            DerivedCategory.Q.map ((pointSectionsTensorComplex D.k l E L
              (IntermediateField.inclusion hEL)).hom.app P)) := by
  let : (completedDerivedScalarExtension.{u, u} l E L
      (IntermediateField.inclusion hEL) (Spec (.of D.k))).CommShift ℤ :=
    pointCompletedScalarCommShift D.k l E L (IntermediateField.inclusion hEL)
  have hδ : NatTrans.CommShift
      (pointOrdinaryDerivedComparison D.k l E L (IntermediateField.inclusion hEL)).inv ℤ := by
    simpa only [Iso.symm_hom] using Functor.CommShift.ofIso_compatibility
      (pointOrdinaryDerivedComparison D.k l E L (IntermediateField.inclusion hEL)).symm ℤ
  have hθ : NatTrans.CommShift
      (pointDerivedSectionsTensor D.k l E L (IntermediateField.inclusion hEL)).hom ℤ := by
    dsimp only [pointDerivedSectionsTensor, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  constructor
  · intro m
    exact NatTrans.shift_app_comm _ m K.obj
  · intro P _hP _hflat e
    refine ⟨?_, ?_, ?_⟩
    · intro r b a
      exact (pointSectionsTensor_existsUnique D.k l E L
        (IntermediateField.inclusion hEL)).exists.choose_spec (P.X r) b a
    · intro m
      change ((pointSectionsTensorSource D.k l E L
        (IntermediateField.inclusion hEL)).mapCochainComplexShiftIso m).hom.app P ≫
          ((NatTrans.mapHomologicalComplex
            (pointSectionsTensor D.k l E L (IntermediateField.inclusion hEL)).hom
            (.up ℤ)).app P)⟦m⟧' = _
      exact NatTrans.shift_app_comm _ m P
    · erw [(pointDerivedSectionsTensor D.k l E L
          (IntermediateField.inclusion hEL)).hom.naturality_assoc e.hom,
        ← Functor.map_comp_assoc, e.hom_inv_id]
      simp only [CategoryTheory.Functor.map_id]
      dsimp only [pointDerivedSectionsTensor, pointSectionsTensorSourceFactors,
        pointSectionsTensorTargetFactors, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
      congr 1
      exact Functor.mapDerivedCategoryNatIso_fac _ P

end WeilConjectures
