/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated

/-!
# The derived tensor product commutes with shifts

Let `C` be an abelian monoidal category whose derived category `D(C)` carries the derived
tensor product `- ⊗ᴸ -` obtained from the K-flat left derivability structure (see
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`). This file shows that
`K ⊗ᴸ -` and `- ⊗ᴸ K` commute with the shift by `ℤ`, for every `K : D(C)`; in particular
`X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧`.

The proof goes as follows.

1. If `P` is a K-flat complex, the comparison `Qh.obj P ⊗ᴸ Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an
   isomorphism for *every* `Z` (`DerivedMonoidal.isIso_counit_app_app_of_kFlat_left`), so
   `Qh.obj P ⊗ᴸ -` is a lifting of `(P ⊗ -) ⋙ Qh` through the localization functor `Qh`.
   As `P ⊗ -` commutes with the shift on the homotopy category
   (`WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated`), so
   does `Qh.obj P ⊗ᴸ -`, by `Functor.commShiftOfLocalization`.
2. Every object `K : D(C)` is isomorphic to `Qh.obj P` for some K-flat complex `P`
   (`DerivedCategory.exists_kFlat_iso`), and the structure is transported along the induced
   isomorphism `Qh.obj P ⊗ᴸ - ≅ K ⊗ᴸ -` by `Functor.CommShift.ofIso`.

The same argument applies to `- ⊗ᴸ K`.

## Main definitions

- `DerivedCategory.commShiftTensorLeft` : the instance
  `((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ`.
- `DerivedCategory.commShiftTensorRight` : the instance
  `((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ`.
- `DerivedCategory.shiftTensorShiftIso` : the isomorphism `X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧`.
- `DerivedCategory.commShiftTensorLeftOfHasFunctorialFlatResolution`,
  `DerivedCategory.commShiftTensorRightOfHasFunctorialFlatResolution` : the same instances
  under the hypotheses of `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`
  (a monoidal closed braided Grothendieck abelian category with functorial flat
  resolutions), where the `GradedObject` hypotheses are not available to instance search.

## Implementation notes

The K-flat complex `P` in step 2 is chosen noncanonically (via `Exists.choose`), so the
commutation isomorphisms of `K ⊗ᴸ -` depend on this choice; no compatibility of the two
structures with each other, nor with the triangulated structure, is established here.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- Every object of the derived category is isomorphic to the image of a K-flat complex. -/
lemma exists_kFlat_iso (K : DerivedCategory C) :
    ∃ (P : HomotopyCategory C (ComplexShape.up ℤ)),
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P ∧
        Nonempty (Qh.obj P ≅ K) := by
  have R : (HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage K) :=
    Classical.arbitrary _
  have := Localization.inverts Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso K⟩⟩

variable (P : HomotopyCategory C (ComplexShape.up ℤ))

/-- The comparison `Qh.obj P ⊗ᴸ Qh.obj Z ⟶ Qh.obj (P ⊗ Z)`, natural in `Z`. -/
noncomputable def tensorLeftCounit :
    Qh ⋙ (curriedTensor _).obj (Qh.obj P) ⟶ (curriedTensor _).obj P ⋙ Qh :=
  Functor.bifunctorCounit₁ (Functor.LaxMonoidal.μNatTrans Qh) P

/-- The comparison `Qh.obj Z ⊗ᴸ Qh.obj P ⟶ Qh.obj (Z ⊗ P)`, natural in `Z`. -/
noncomputable def tensorRightCounit :
    Qh ⋙ (curriedTensor _).flip.obj (Qh.obj P) ⟶ (curriedTensor _).flip.obj P ⋙ Qh :=
  Functor.bifunctorCounit₂ (Functor.LaxMonoidal.μNatTrans Qh) P

/-- If `P` is K-flat, the comparison `Qh.obj P ⊗ᴸ Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an
isomorphism for every `Z`. -/
lemma isIso_tensorLeftCounit (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    IsIso (tensorLeftCounit P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh _ P Z hP

/-- If `P` is K-flat, the comparison `Qh.obj Z ⊗ᴸ Qh.obj P ⟶ Qh.obj (Z ⊗ P)` is an
isomorphism for every `Z`. -/
lemma isIso_tensorRightCounit (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    IsIso (tensorRightCounit P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_right Qh _ Z P hP

/-- For a K-flat complex `P`, the functor `Qh.obj P ⊗ᴸ -` commutes with the shift, being
induced through the localization `Qh` by the functor `(P ⊗ -) ⋙ Qh`, which does. -/
@[instance_reducible]
noncomputable def commShiftTensorLeftQhObj
    (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    ((curriedTensor (DerivedCategory C)).obj (Qh.obj P)).CommShift ℤ :=
  have := isIso_tensorLeftCounit P hP
  letI : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj P ⋙ Qh) ((curriedTensor _).obj (Qh.obj P)) :=
    ⟨asIso (tensorLeftCounit P)⟩
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((curriedTensor _).obj P ⋙ Qh) _

/-- For a K-flat complex `P`, the functor `- ⊗ᴸ Qh.obj P` commutes with the shift, being
induced through the localization `Qh` by the functor `(- ⊗ P) ⋙ Qh`, which does. -/
@[instance_reducible]
noncomputable def commShiftTensorRightQhObj
    (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    ((curriedTensor (DerivedCategory C)).flip.obj (Qh.obj P)).CommShift ℤ :=
  have := isIso_tensorRightCounit P hP
  letI : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj P ⋙ Qh) ((curriedTensor _).flip.obj (Qh.obj P)) :=
    ⟨asIso (tensorRightCounit P)⟩
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((curriedTensor _).flip.obj P ⋙ Qh) _

/-- The derived tensor product `K ⊗ᴸ -` commutes with the shift by `ℤ`. The structure is
transported from `commShiftTensorLeftQhObj` along an isomorphism `Qh.obj P ≅ K` with `P`
a (noncanonically chosen) K-flat complex. -/
noncomputable instance commShiftTensorLeft (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ :=
  letI := commShiftTensorLeftQhObj _ (exists_kFlat_iso K).choose_spec.1
  Functor.CommShift.ofIso ((curriedTensor _).mapIso (exists_kFlat_iso K).choose_spec.2.some) ℤ

/-- The derived tensor product `- ⊗ᴸ K` commutes with the shift by `ℤ`. The structure is
transported from `commShiftTensorRightQhObj` along an isomorphism `Qh.obj P ≅ K` with `P`
a (noncanonically chosen) K-flat complex. -/
noncomputable instance commShiftTensorRight (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ :=
  letI := commShiftTensorRightQhObj _ (exists_kFlat_iso K).choose_spec.1
  Functor.CommShift.ofIso
    ((curriedTensor _).flip.mapIso (exists_kFlat_iso K).choose_spec.2.some) ℤ

/-- The derived tensor product, as `X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧`. -/
noncomputable def shiftTensorShiftIso (X Y : DerivedCategory C) (a b : ℤ) :
    X⟦a⟧ ⊗ Y⟦b⟧ ≅ (X ⊗ Y)⟦a + b⟧ :=
  (((curriedTensor (DerivedCategory C)).flip.obj (Y⟦b⟧)).commShiftIso a).app X ≪≫
    (shiftFunctor _ a).mapIso ((((curriedTensor _).obj X).commShiftIso b).app Y) ≪≫
    (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).symm.app _

section GrothendieckAbelian

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- For a monoidal closed braided Grothendieck abelian category `C` with functorial flat
resolutions, `K ⊗ᴸ -` commutes with the shift on `DerivedCategory C`. -/
noncomputable instance commShiftTensorLeftOfHasFunctorialFlatResolution
    (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ :=
  commShiftTensorLeft K

/-- For a monoidal closed braided Grothendieck abelian category `C` with functorial flat
resolutions, `- ⊗ᴸ K` commutes with the shift on `DerivedCategory C`. -/
noncomputable instance commShiftTensorRightOfHasFunctorialFlatResolution
    (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ :=
  commShiftTensorRight K

end GrothendieckAbelian

end DerivedCategory
