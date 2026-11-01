/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData

/-! # Localization tensorators on K-flat cochain complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace WeilConjectures.PurityFiniteSetting

private theorem localizationTensor_isIso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{w} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    [HasColimitsOfSize.{0, 0} A]
    (C D : CochainComplex A ℤ)
    (hD : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat D) :
    IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q C D) := by
  have : IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj D)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right _root_.DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff D).2 hD)
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh _ _ ≫
      _root_.DerivedCategory.Qh.map _) ≫ _)
  infer_instance

/-- The native localization tensorator with its actual morphism type written explicitly.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-cochain-localization-tensor-invertible). -/
@[irreducible] def cochainLocalizationTensor
    {A : Type (u + 1)} [CommRing A] (T : AlgebraicGeometry.Scheme.{u})
    (C D : CochainComplex
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (_root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj C) ⊗
        (_root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj D) ⟶
      _root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj (C ⊗ D) :=
  Functor.LaxMonoidal.μ _root_.DerivedCategory.Q C D

/-- The cochain localization tensorator is invertible when its right input is K-flat.
Source: Stacks 07A4 and 0FPT, calculation of derived tensor on K-flat complexes.
(blueprint: lem-pur-cochain-localization-tensor-invertible).
Proof: the quotient into the homotopy category preserves K-flatness. The tensor
counit defining the lax monoidal structure of Qh is invertible with K-flat right
input. The quotient functor is strong monoidal, and the remaining factors of Q's
tensorator are its isomorphisms. Functoriality and composition finish. -/
theorem cochainLocalizationTensor_isIso
    {A : Type (u + 1)} [CommRing A] (T : AlgebraicGeometry.Scheme.{u})
    (C D : CochainComplex
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
    (hD : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat D) :
    IsIso (cochainLocalizationTensor T C D) := by
  unfold cochainLocalizationTensor
  exact localizationTensor_isIso C D hD

end WeilConjectures.PurityFiniteSetting
