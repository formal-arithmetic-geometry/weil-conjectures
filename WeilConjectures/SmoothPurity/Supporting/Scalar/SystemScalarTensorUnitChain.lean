/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnitStrict
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionTensorUnit
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives

/-! # Strict scalar extension of the coefficient-ring complex

On the ringed sequence site, extension of scalars sends the coefficient ring in degree zero
to the coefficient ring in degree zero, and the strict scalar tensor comparison is compatible
with the unit multiplication maps `x ⊗ a ↦ a • x` and `a ⊗ x ↦ a • x`.
Source: Stacks Project, Tags 03EL and 07A4
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

open Opposite ScalarExtensionTower

section Chain
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- The coefficient ring of the sequence site, placed in degree zero. -/
abbrev sequenceUnitComplex : Complex l E W :=
  ringedTensorUnitComplex.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

/-- The coefficient-ring complex is a flat-term K-flat complex. -/
theorem sequenceUnitComplex_good : Good l E W (sequenceUnitComplex l E W) :=
  ⟨CategoryTheory.RingedForgetTensorTransposition.unit_kflat _ _,
    CategoryTheory.RingedForgetTensorTransposition.unit_flat _ _⟩

/-- Extension of scalars of the coefficient-ring complex is the coefficient-ring complex,
by an isomorphism sending `1 ⊗ a` to the image of `a`. -/
theorem sequenceUnitComplexScalarIso_exists :
    ∃ c : (scalar l E L ι W).obj (sequenceUnitComplex l E W) ≅ sequenceUnitComplex l L W,
      ∀ (V : (ℕ × W.ProEt)ᵒᵖ) (a : (coefficientSequenceCommRingSheaf l E W).obj.obj V),
        (c.hom.f 0).val.app V (integralComparisonSequenceTensorSection l E L ι W _ V 1
          (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) V a)) =
        ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l L W) V
          ((integralComparisonSequenceScalarMap l E L ι W).hom.app V a) := by
  let α := (sheafCompose (coefficientSequenceTopology (ProEt.topology W))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralComparisonSequenceScalarMap l E L ι W)
  let c0 := ((scalar_adj l E L ι W).homEquiv _ _).symm
    (SheafOfModules.unitToRestrictScalarsUnit α)
  have : IsIso c0 := SheafOfModules.isIso_unitToRestrictScalarsUnit_transpose α _
  have h0 (V : (ℕ × W.ProEt)ᵒᵖ) (x) :
      c0.val.app V (integralComparisonSequenceTensorSection l E L ι W _ V 1 x) =
        (SheafOfModules.unitToRestrictScalarsUnit α).val.app V x := by
    rw [← scalar_transpose_section]
    dsimp only [c0]
    rw [Equiv.apply_symm_apply]
  refine ⟨(HomologicalComplex.singleMapHomologicalComplex _ (ComplexShape.up ℤ) 0).app _ ≪≫
    (HomologicalComplex.single (coefficientSequenceModules l L W) (ComplexShape.up ℤ) 0).mapIso
      (asIso c0), ?_⟩
  intro V a
  have hc : ((HomologicalComplex.singleMapHomologicalComplex _ (ComplexShape.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single (coefficientSequenceModules l L W) (ComplexShape.up ℤ) 0).mapIso
        (asIso c0)).hom.f 0 =
      (integralComparisonSequenceScalarModel l E L ι W).E.map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫ c0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv := by
    rw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Functor.mapIso_hom, asIso_hom,
      HomologicalComplex.single_map_f_self]
    erw [Category.assoc, Iso.inv_hom_id_assoc]
  erw [hc]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalar_section_naturality]
  unfold ringedTensorUnitSection
  erw [SheafOfModules.iso_hom_inv_val_app_apply, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, h0]
  rfl

/-- Sections of a zero sheaf of modules vanish. -/
theorem sheafSections_eq_zero_of_isZero {M : coefficientSequenceModules l E W}
    (hM : Limits.IsZero M)
    (V : (ℕ × W.ProEt)ᵒᵖ) (y : M.val.obj V) : y = 0 := by
  have h := congrArg (fun f : M ⟶ M ↦ f.val.app V y) (hM.eq_of_src (𝟙 M) 0)
  exact h.trans rfl

/-- A tensor generator with a vanishing right factor vanishes. -/
theorem tensorGenerator_zero_right (P Q : Complex l E W) (p q k : ℤ) (h : p + q = k)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj V) :
    coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) P Q p q k h V x 0 = 0 := by
  unfold coefficientTensorGenerator
  rw [TensorProduct.tmul_zero]
  erw [map_zero, map_zero]

/-- A tensor generator with a vanishing left factor vanishes. -/
theorem tensorGenerator_zero_left (P Q : Complex l E W) (p q k : ℤ) (h : p + q = k)
    (V : (ℕ × W.ProEt)ᵒᵖ) (y : (Q.X q).val.obj V) :
    coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) P Q p q k h V 0 y = 0 := by
  unfold coefficientTensorGenerator
  rw [TensorProduct.zero_tmul]
  erw [map_zero, map_zero]

/-- Every degree-zero section of the coefficient-ring complex is a ring section. -/
theorem sequenceUnitComplex_section_surjective (V : (ℕ × W.ProEt)ᵒᵖ)
    (y : ((sequenceUnitComplex l E W).X 0).val.obj V) :
    ∃ a : (coefficientSequenceCommRingSheaf l E W).obj.obj V,
      ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) V a = y := by
  refine ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E W)))).hom.val.app V y, ?_⟩
  unfold ringedTensorUnitSection
  exact SheafOfModules.iso_inv_hom_val_app_apply _ V y

/-- The scalar unit tensor section is balanced along the coefficient inclusion. -/
theorem tensorSection_one_smul (M : coefficientSequenceModules l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (a : (coefficientSequenceCommRingSheaf l E W).obj.obj V) (x : M.val.obj V) :
    integralComparisonSequenceTensorSection l E L ι W M V 1 (a • x) =
      (integralComparisonSequenceScalarMap l E L ι W).hom.app V a •
        integralComparisonSequenceTensorSection l E L ι W M V 1 x := by
  have h (z : M.val.obj V) : integralComparisonSequenceTensorSection l E L ι W M V 1 z =
      (((scalar_adj l E L ι W).homEquiv _ _) (𝟙 _)).val.app V z := by
    rw [scalar_transpose_section]
    rfl
  rw [h, h]
  exact (((scalar_adj l E L ι W).homEquiv _ _) (𝟙 _)).val.app V |>.hom.map_smul a x


/-- The scalar unit tensor section of zero vanishes. -/
theorem tensorSection_one_zero (M : coefficientSequenceModules l E W) (V : (ℕ × W.ProEt)ᵒᵖ) :
    integralComparisonSequenceTensorSection l E L ι W M V 1 0 = 0 := by
  have h := tensorSection_one_smul l E L ι W M V 0 0
  rwa [zero_smul, map_zero, zero_smul] at h
theorem sigmaDegree (P Q : Complex l E W) (p q k : ℤ) (h : p + q = k)
    (V : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    ((((comparisons l).sigma E L ι W).hom.app (P, Q)).f k).val.app V (
      integralComparisonSequenceTensorSection l E L ι W
        (((tensor l E W).obj (P, Q)).X k) V 1
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h V x y)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W)
        ((scalar l E L ι W).obj P) ((scalar l E L ι W).obj Q) p q k h V
        (integralComparisonSequenceTensorSection l E L ι W (P.X p) V 1 x)
        (integralComparisonSequenceTensorSection l E L ι W (Q.X q) V 1 y) := by
  subst k
  exact (comparisons l).sigma_formula E L ι W P Q p q V 1 x y

set_option maxHeartbeats 800000 in
-- Section maps pass through the scalar adjunction and the total-tensor sheafification.
/-- The strict scalar tensor comparison is compatible with right multiplication by the
coefficient ring. -/
theorem scalarRightUnitStrict
    (c : (scalar l E L ι W).obj (sequenceUnitComplex l E W) ≅ sequenceUnitComplex l L W)
    (hc : ∀ (V : (ℕ × W.ProEt)ᵒᵖ) (a : (coefficientSequenceCommRingSheaf l E W).obj.obj V),
      (c.hom.f 0).val.app V (integralComparisonSequenceTensorSection l E L ι W _ V 1
        (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) V a)) =
      ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W) V
        ((integralComparisonSequenceScalarMap l E L ι W).hom.app V a))
    (P : Complex l E W)
    (rE : (tensor l E W).obj (P, sequenceUnitComplex l E W) ⟶ P)
    (hrE : ∀ (n : ℤ) (h : n + 0 = n) (U : (ℕ × W.ProEt)ᵒᵖ)
      (a : (coefficientSequenceCommRingSheaf l E W).obj.obj U) (x : (P.X n).val.obj U),
      (rE.f n).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        P (sequenceUnitComplex l E W) n 0 n h U x
        (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) U a)) = a • x)
    (rL : (tensor l L W).obj ((scalar l E L ι W).obj P, sequenceUnitComplex l L W) ⟶
      (scalar l E L ι W).obj P)
    (hrL : ∀ (n : ℤ) (h : n + 0 = n) (U : (ℕ × W.ProEt)ᵒᵖ)
      (a : (coefficientSequenceCommRingSheaf l L W).obj.obj U)
      (x : (((scalar l E L ι W).obj P).X n).val.obj U),
      (rL.f n).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l L W)
        ((scalar l E L ι W).obj P) (sequenceUnitComplex l L W) n 0 n h U x
        (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l L W) U a)) = a • x) :
    ((comparisons l).sigma E L ι W).hom.app (P, sequenceUnitComplex l E W) ≫
      (tensor l L W).map (Prod.mkHom (𝟙 _) c.hom) ≫ rL = (scalar l E L ι W).map rE := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l E L ι W).homEquiv _ _).injective
  apply total_tensor_sections_ext l E W P (sequenceUnitComplex l E W) n
  intro p q hpq V x y
  erw [scalar_transpose_section, scalar_transpose_section]
  by_cases hq : q = 0
  · subst hq
    obtain rfl : n = p := by omega
    obtain ⟨a, rfl⟩ := sequenceUnitComplex_section_surjective l E W V y
    erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, sigmaDegree, generator_map,
      HomologicalComplex.id_f, hc, hrL, Functor.mapHomologicalComplex_map_f,
      scalar_section_naturality]
    rw [hrE n hpq V a x, tensorSection_one_smul]
    rfl
  · have hy := sheafSections_eq_zero_of_isZero l E W
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq) V y
    subst hy
    rw [tensorGenerator_zero_right, tensorSection_one_zero]
    erw [map_zero, map_zero]

set_option maxHeartbeats 800000 in
-- Section maps pass through the scalar adjunction and the total-tensor sheafification.
/-- The strict scalar tensor comparison is compatible with left multiplication by the
coefficient ring. -/
theorem scalarLeftUnitStrict
    (c : (scalar l E L ι W).obj (sequenceUnitComplex l E W) ≅ sequenceUnitComplex l L W)
    (hc : ∀ (V : (ℕ × W.ProEt)ᵒᵖ) (a : (coefficientSequenceCommRingSheaf l E W).obj.obj V),
      (c.hom.f 0).val.app V (integralComparisonSequenceTensorSection l E L ι W _ V 1
        (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) V a)) =
      ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l L W) V
        ((integralComparisonSequenceScalarMap l E L ι W).hom.app V a))
    (P : Complex l E W)
    (lE : (tensor l E W).obj (sequenceUnitComplex l E W, P) ⟶ P)
    (hlE : ∀ (n : ℤ) (h : 0 + n = n) (U : (ℕ × W.ProEt)ᵒᵖ)
      (a : (coefficientSequenceCommRingSheaf l E W).obj.obj U) (x : (P.X n).val.obj U),
      (lE.f n).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        (sequenceUnitComplex l E W) P 0 n n h U
        (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) U a) x) = a • x)
    (lL : (tensor l L W).obj (sequenceUnitComplex l L W, (scalar l E L ι W).obj P) ⟶
      (scalar l E L ι W).obj P)
    (hlL : ∀ (n : ℤ) (h : 0 + n = n) (U : (ℕ × W.ProEt)ᵒᵖ)
      (a : (coefficientSequenceCommRingSheaf l L W).obj.obj U)
      (x : (((scalar l E L ι W).obj P).X n).val.obj U),
      (lL.f n).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l L W)
        (sequenceUnitComplex l L W) ((scalar l E L ι W).obj P) 0 n n h U
        (ringedTensorUnitSection.{u + 1, u, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l L W) U a) x) = a • x) :
    ((comparisons l).sigma E L ι W).hom.app (sequenceUnitComplex l E W, P) ≫
      (tensor l L W).map (Prod.mkHom c.hom (𝟙 _)) ≫ lL = (scalar l E L ι W).map lE := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l E L ι W).homEquiv _ _).injective
  apply total_tensor_sections_ext l E W (sequenceUnitComplex l E W) P n
  intro p q hpq V y x
  erw [scalar_transpose_section, scalar_transpose_section]
  by_cases hp : p = 0
  · subst hp
    obtain rfl : n = q := by omega
    obtain ⟨a, rfl⟩ := sequenceUnitComplex_section_surjective l E W V y
    erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, sigmaDegree, generator_map,
      HomologicalComplex.id_f, hc, hlL, Functor.mapHomologicalComplex_map_f,
      scalar_section_naturality]
    rw [hlE n hpq V a x, tensorSection_one_smul]
    rfl
  · have hy := sheafSections_eq_zero_of_isZero l E W
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ p hp) V y
    subst hy
    rw [tensorGenerator_zero_left, tensorSection_one_zero]
    erw [map_zero, map_zero]

end Chain

end WeilConjectures
