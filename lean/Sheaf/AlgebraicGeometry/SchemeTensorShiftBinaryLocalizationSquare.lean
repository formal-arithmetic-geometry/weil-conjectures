/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # Binary localization square for the first tensor shift
Source: Stacks Project, Tag 06YH, localization of total tensor products.
(blueprint: lem-sc-scheme-tensor-shift-binary-localization-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w u'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace DerivedCategory.IndependentTensorShift

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{u'} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]

local instance (P T : CochainComplex C ℤ) :
    CochainComplex.HasMapBifunctor P T (curriedTensor C) := inferInstance

noncomputable local instance : MonoidalCategory (CochainComplex C ℤ) := inferInstance

noncomputable local instance : MonoidalCategory (DerivedCategory C) := inferInstance

attribute [local instance] commShift₂CurriedTensor
open DerivedCategory.TensorCommShift₂

private theorem squareL (P : CochainComplex.KFlat C) (T : CochainComplex C ℤ) :
    ((tensorRight ((L C).obj T)).commShiftIso (1 : ℤ)).hom.app ((LKFlat C).obj P) ≫
      (Functor.LaxMonoidal.μ (L C) P.obj T)⟦(1 : ℤ)⟧' ≫
      ((L C).commShiftIso (1 : ℤ)).inv.app (P.obj ⊗ T) =
    (((L C).commShiftIso (1 : ℤ)).inv.app P.obj) ▷ (L C).obj T ≫
      Functor.LaxMonoidal.μ (L C) (P.obj⟦(1 : ℤ)⟧) T ≫
      (L C).map (CochainComplex.mapBifunctorShift₁Iso P.obj T (curriedTensor C) 1).hom := by
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (L C) (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip T
  have h := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
    (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip T) (1 : ℤ) P
  rw [Functor.commShiftIso_comp_hom_app] at h
  let a := ((CochainComplex.ιKFlat C).commShiftIso (1 : ℤ)).hom.app P
  have hl (V : CochainComplex.KFlat C) :
      (Functor.CommShift₂OfLocalization.liftingIsoApp (L C) (LKFlat C)
        (HomologicalComplex.quasiIso C (.up ℤ))
        (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
        (F C).flip (curriedTensor (DerivedCategory C)).flip T).app V =
      Functor.LaxMonoidal.μ (L C) V.obj T := by
    simp only [Functor.LaxMonoidal.comp_μ]
    change _ = _ ≫ Qh.map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have hf : (((F C).flip.obj T).commShiftIso (1 : ℤ)).hom.app P =
      (L C).map (a ▷ T ≫
        (CochainComplex.mapBifunctorShift₁Iso P.obj T (curriedTensor C) 1).hom) ≫
        ((L C).commShiftIso (1 : ℤ)).hom.app _ := by
    erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
    rfl
  have hk : ((LKFlat C).commShiftIso (1 : ℤ)).hom.app P =
      (L C).map a ≫ ((L C).commShiftIso (1 : ℤ)).hom.app P.obj :=
    Functor.commShiftIso_comp_hom_app _ _ _ _
  rw [hl, hl, hf, hk] at h
  simp only [Functor.map_comp, Category.assoc] at h
  change (L C).map a ▷ (L C).obj T ≫
      (((L C).commShiftIso (1 : ℤ)).hom.app P.obj) ▷ (L C).obj T ≫
      ((tensorRight ((L C).obj T)).commShiftIso (1 : ℤ)).hom.app ((L C).obj P.obj) ≫
      (Functor.LaxMonoidal.μ (L C) P.obj T)⟦(1 : ℤ)⟧' = _ at h
  erw [← Functor.LaxMonoidal.μ_natural_left_assoc] at h
  rw [CategoryTheory.cancel_epi] at h
  have h' := congrArg (fun f ↦
    (((L C).commShiftIso (1 : ℤ)).inv.app P.obj) ▷ (L C).obj T ≫ f ≫
      ((L C).commShiftIso (1 : ℤ)).inv.app (P.obj ⊗ T)) h
  simp only [Category.assoc] at h'
  change _ = _ ≫ _ ≫ _ ≫
    ((L C).commShiftIso (1 : ℤ)).hom.app (P.obj ⊗ T) ≫
      ((L C).commShiftIso (1 : ℤ)).inv.app (P.obj ⊗ T) at h'
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id_app,
    id_whiskerRight, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id] at h'
  exact h'

private theorem squareQ (P T : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    ((tensorRight (Q.obj T)).commShiftIso (1 : ℤ)).hom.app (Q.obj P) ≫
      (Functor.LaxMonoidal.μ Q P T)⟦(1 : ℤ)⟧' ≫
      (Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ T) =
    ((Q.commShiftIso (1 : ℤ)).inv.app P) ▷ Q.obj T ≫
      Functor.LaxMonoidal.μ Q (P⟦(1 : ℤ)⟧) T ≫
      Q.map (CochainComplex.mapBifunctorShift₁Iso P T (curriedTensor C) 1).hom := by
  have hμ (A B : CochainComplex C ℤ) :
      Functor.LaxMonoidal.μ Q A B = Functor.LaxMonoidal.μ (L C) A B := by
    change (𝟙 _ ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ (L C) A B ≫ 𝟙 _ = _
    simp
  have hη (A : CochainComplex C ℤ) :
      (Q.commShiftIso (1 : ℤ)).inv.app A = ((L C).commShiftIso (1 : ℤ)).inv.app A := by
    rw [Functor.CommShift.ofIso_commShiftIso_inv_app]
    change (𝟙 _)⟦(1 : ℤ)⟧' ≫ ((L C).commShiftIso (1 : ℤ)).inv.app A ≫ 𝟙 _ = _
    simp
  simp only [hμ, hη]
  exact squareL C ⟨P, hP⟩ T

end DerivedCategory.IndependentTensorShift

namespace AlgebraicGeometry

variable (X : Scheme.{u})

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_symmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance SchemeTensorShiftBinaryLocalizationSquare_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
local instance SchemeTensorShiftBinaryLocalizationSquare_hasColimitsOfSize :
    HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink.{0, 0, u, u} _
local instance SchemeTensorShiftBinaryLocalizationSquare_hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance SchemeTensorShiftBinaryLocalizationSquare_hasDerivedMonoidalCategory :
    DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

local instance SchemeTensorShiftBinaryLocalizationSquare_hasTensor (A B : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) : A.HasTensor B := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasTensor₄ObjExt (A B C D : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasGoodTensor₁₂Tensor
    (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasGoodTensorTensor₂₃
    (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasMapBifunctor (A B : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor A B
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) := inferInstance

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalCategory2 :
    MonoidalCategory
    (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := inferInstance

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalCategory3 :
    MonoidalCategory (schemeDerivedCategory X) :=
  schemeDerivedTensorMonoidal X

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_laxMonoidal :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  Functor.LaxMonoidal.ofIso (DerivedCategory.quotientCompQhIso _)

set_option linter.unusedVariables false in
/-- The first-variable tensor shift agrees with localization on a K-flat first factor.
Source: Stacks Project, Tag 06YH; the explicit localization construction
`Functor.CommShift₂OfLocalization.commShift_liftingIsoApp`.
(blueprint: lem-sc-scheme-tensor-shift-binary-localization-square).

Proof. Restrict the first variable to K-flat complexes. The natural comparison
from localized tensor to localization of total tensor is `liftingIsoHom` and
commutes with translation by the defining localization construction. Evaluate
its flipped component at the second complex. Expand the shift of the inclusion
of K-flat complexes, and cancel its invertible comparison by naturality of the
tensorator. This gives the square for quotient followed by Qh. Transport along
`quotientCompQhIso`, whose tensorator and shift structures are transported along
this same isomorphism, to obtain the displayed square for Q. This is a binary
square, independent of any associator coherence; it also holds for zero complexes. -/
theorem schemeTensorShift_binary_localization_square
    (P T : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat P) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((tensorRight (DerivedCategory.Q.obj T)).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj P) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Q P T)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ T) =
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app P) ▷ DerivedCategory.Q.obj T ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q (P⟦(1 : ℤ)⟧) T ≫
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso P T
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  exact DerivedCategory.IndependentTensorShift.squareQ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) P T hP

end AlgebraicGeometry
