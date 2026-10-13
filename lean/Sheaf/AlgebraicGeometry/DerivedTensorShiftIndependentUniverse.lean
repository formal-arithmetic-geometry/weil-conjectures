/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Tensor shifts with independent localization and Grothendieck universes

Source: Stacks Project, Tag 06YH, K-flat localization of total tensor products.
(blueprint: lem-sc-derived-tensor-shift-independent-universe).
The upstream shift construction unnecessarily identifies these two universes.
This is the same localization construction with the two parameters separated.
-/

@[expose] public section
set_option autoImplicit false
universe u v w s
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory.IndependentTensorShift

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

variable [HasColimitsOfSize.{0, 0} C]

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace TensorCommShift₂

/-- The localization functor `K(C) ⥤ D(C)` precomposed with the quotient
`CochainComplex C ℤ ⥤ K(C)`. -/
noncomputable abbrev L : CochainComplex C ℤ ⥤ DerivedCategory C :=
  HomotopyCategory.quotient C (.up ℤ) ⋙ Qh

instance : (L C).IsLocalization (HomologicalComplex.quasiIso C (.up ℤ)) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C).symm

/-- The localization functor restricted to K-flat cochain complexes. -/
noncomputable abbrev LKFlat : CochainComplex.KFlat C ⥤ DerivedCategory C :=
  CochainComplex.ιKFlat C ⋙ L C

instance : (LKFlat C).IsLocalization (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat :=
  inferInstanceAs (((HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.functor ⋙
    L C).IsLocalization _)

noncomputable instance : (curriedTensor (CochainComplex C ℤ)).CommShift₂Int :=
  inferInstanceAs ((curriedTensor C).map₂CochainComplex.CommShift₂Int)

/-- The tensor product of a K-flat complex with a complex, followed by the localization functor:
the bifunctor which is localized to the derived tensor product. -/
noncomputable abbrev F : CochainComplex.KFlat C ⥤ CochainComplex C ℤ ⥤ DerivedCategory C :=
  (CochainComplex.ιKFlat C ⋙ curriedTensor (CochainComplex C ℤ)) ⋙
    (Functor.whiskeringRight _ _ _).obj (L C)

noncomputable instance : (F C).CommShift₂Int := Functor.CommShift₂.postcompInt _ _

/-- The comparison `Qh P ⊗ᴸ Qh K ⟶ Qh (P ⊗ K)` for a K-flat complex `P` and a complex `K`. -/
noncomputable def liftingIsoHom :
    (((Functor.whiskeringLeft₂ _).obj (LKFlat C)).obj (L C)).obj
      (curriedTensor (DerivedCategory C)) ⟶ F C :=
  (((Functor.whiskeringLeft₂ (DerivedCategory C)).obj
    (CochainComplex.ιKFlat C ⋙ HomotopyCategory.quotient C _)).obj
      (HomotopyCategory.quotient C _)).map (Functor.LaxMonoidal.μNatTrans Qh)

instance : IsIso (liftingIsoHom C) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh _ _ _
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2)

noncomputable instance lifting :
    Localization.Lifting₂ (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (HomologicalComplex.quasiIso C (.up ℤ)) (F C) (curriedTensor (DerivedCategory C)) where
  iso := asIso (liftingIsoHom C)

end TensorCommShift₂

open DerivedCategory.IndependentTensorShift.TensorCommShift₂ in
/-- The derived tensor product commutes with the shifts by `ℤ` in both variables, with the
sign `(-1) ^ (p * q)` when shifting the first variable by `p` and the second by `q`. It is
induced through the localization functors by the commutation with shifts of the tensor
product of cochain complexes (`Functor.commShift₂OfLocalization`).
Source: Stacks Project, Tag 06YH, localization of total tensor products.
(blueprint: lem-sc-derived-tensor-shift-independent-universe). -/
@[instance_reducible]
noncomputable def commShift₂CurriedTensor :
    (curriedTensor (DerivedCategory C)).CommShift₂Int :=
  Functor.commShift₂OfLocalization (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (HomologicalComplex.quasiIso C (.up ℤ)) (F C) _ .int

attribute [local instance] commShift₂CurriedTensor


end DerivedCategory.IndependentTensorShift
