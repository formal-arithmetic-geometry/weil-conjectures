/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap

/-!
# Composition of the functors induced on rationalizations along ring morphisms

A triangulated functor `F : C ⥤ D` which is linear along a ring morphism `ψ : R →+* R'` induces
`Rationalization.mapOfRingHom ψ hM F hF` on the rationalizations
(`WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap`). This file shows that the
construction is compatible with composition and identities up to isomorphism: an isomorphism
`F₁ ⋙ F₂ ≅ F` induces `mapOfRingHom F₁ ⋙ mapOfRingHom F₂ ≅ mapOfRingHom F`, and an isomorphism
`F ≅ 𝟭` induces `mapOfRingHom F ≅ 𝟭`. Both are characterized by their values on the image of
the localization functor.

## Main definitions

- `CategoryTheory.Rationalization.mapOfRingHomCompIso`: compatibility with composition.
- `CategoryTheory.Rationalization.mapOfRingHomIdIso`: compatibility with identities.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Rationalization

variable {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  {M₁ : Submonoid R₁} {M₂ : Submonoid R₂} {M₃ : Submonoid R₃}
  {C₁ : Type*} [Category C₁] [Preadditive C₁] [Linear R₁ C₁] [HasZeroObject C₁]
  [HasShift C₁ ℤ] [∀ n : ℤ, (shiftFunctor C₁ n).Additive]
  [∀ n : ℤ, (shiftFunctor C₁ n).Linear R₁] [Pretriangulated C₁] [IsTriangulated C₁]
  {C₂ : Type*} [Category C₂] [Preadditive C₂] [Linear R₂ C₂] [HasZeroObject C₂]
  [HasShift C₂ ℤ] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor C₂ n).Linear R₂] [Pretriangulated C₂] [IsTriangulated C₂]
  {C₃ : Type*} [Category C₃] [Preadditive C₃] [Linear R₃ C₃] [HasZeroObject C₃]
  [HasShift C₃ ℤ] [∀ n : ℤ, (shiftFunctor C₃ n).Additive]
  [∀ n : ℤ, (shiftFunctor C₃ n).Linear R₃] [Pretriangulated C₃] [IsTriangulated C₃]

section Comp

variable (ψ₁ : R₁ →+* R₂) (hM₁ : M₁ ≤ M₂.comap ψ₁) (F₁ : C₁ ⥤ C₂) [F₁.CommShift ℤ]
  [F₁.IsTriangulated] (hF₁ : ∀ (r : R₁) {X Y : C₁} (f : X ⟶ Y), F₁.map (r • f) = ψ₁ r • F₁.map f)
  (ψ₂ : R₂ →+* R₃) (hM₂ : M₂ ≤ M₃.comap ψ₂) (F₂ : C₂ ⥤ C₃) [F₂.CommShift ℤ]
  [F₂.IsTriangulated] (hF₂ : ∀ (r : R₂) {X Y : C₂} (f : X ⟶ Y), F₂.map (r • f) = ψ₂ r • F₂.map f)
  (ψ : R₁ →+* R₃) (hM : M₁ ≤ M₃.comap ψ) (F : C₁ ⥤ C₃) [F.CommShift ℤ]
  [F.IsTriangulated] (hF : ∀ (r : R₁) {X Y : C₁} (f : X ⟶ Y), F.map (r • f) = ψ r • F.map f)

/-- The composite of the functors induced on rationalizations is a lifting of the composite. -/
noncomputable def mapOfRingHomCompFac :
    Q M₁ C₁ ⋙ mapOfRingHom ψ₁ hM₁ F₁ hF₁ ⋙ mapOfRingHom ψ₂ hM₂ F₂ hF₂ ≅
      (F₁ ⋙ F₂) ⋙ Q M₃ C₃ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F₁ ⋙ Q M₂ C₂)
      (mapOfRingHom ψ₁ hM₁ F₁ hF₁)) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F₁ (Localization.Lifting.iso (Q M₂ C₂) (W M₂ C₂) (F₂ ⋙ Q M₃ C₃)
      (mapOfRingHom ψ₂ hM₂ F₂ hF₂)) ≪≫ (Functor.associator _ _ _).symm

/-- An isomorphism `F₁ ⋙ F₂ ≅ F` of functors between the integral categories induces an
isomorphism `mapOfRingHom F₁ ⋙ mapOfRingHom F₂ ≅ mapOfRingHom F` between the functors induced
on the rationalizations. -/
noncomputable def mapOfRingHomCompIso (e : F₁ ⋙ F₂ ≅ F) :
    mapOfRingHom ψ₁ hM₁ F₁ hF₁ ⋙ mapOfRingHom ψ₂ hM₂ F₂ hF₂ ≅ mapOfRingHom ψ hM F hF :=
  letI : Localization.Lifting (Q M₁ C₁) (W M₁ C₁) ((F₁ ⋙ F₂) ⋙ Q M₃ C₃)
      (mapOfRingHom ψ₁ hM₁ F₁ hF₁ ⋙ mapOfRingHom ψ₂ hM₂ F₂ hF₂) :=
    ⟨mapOfRingHomCompFac ψ₁ hM₁ F₁ hF₁ ψ₂ hM₂ F₂ hF₂⟩
  Localization.liftNatIso (Q M₁ C₁) (W M₁ C₁) ((F₁ ⋙ F₂) ⋙ Q M₃ C₃) (F ⋙ Q M₃ C₃) _ _
    (Functor.isoWhiskerRight e _)

/-- The isomorphism `mapOfRingHomCompIso` on the image of an integral object: it is the image
of the integral isomorphism, through the factorizations of the induced functors. -/
lemma mapOfRingHomCompIso_hom_app (e : F₁ ⋙ F₂ ≅ F) (X : C₁) :
    (mapOfRingHomCompIso ψ₁ hM₁ F₁ hF₁ ψ₂ hM₂ F₂ hF₂ ψ hM F hF e).hom.app ((Q M₁ C₁).obj X) =
      (mapOfRingHomCompFac ψ₁ hM₁ F₁ hF₁ ψ₂ hM₂ F₂ hF₂).hom.app X ≫
        (Q M₃ C₃).map (e.hom.app X) ≫
        (Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₃ C₃)
          (mapOfRingHom ψ hM F hF)).inv.app X := by
  simp [mapOfRingHomCompIso, Localization.liftNatIso, Localization.liftNatTrans_app]
  rfl

end Comp

section Id

variable (ψ : R₁ →+* R₁) (hM : M₁ ≤ M₁.comap ψ) (F : C₁ ⥤ C₁) [F.CommShift ℤ]
  [F.IsTriangulated] (hF : ∀ (r : R₁) {X Y : C₁} (f : X ⟶ Y), F.map (r • f) = ψ r • F.map f)

/-- An isomorphism `F ≅ 𝟭` of an endofunctor of the integral category induces an isomorphism
`mapOfRingHom F ≅ 𝟭` of the functor induced on the rationalization. -/
noncomputable def mapOfRingHomIdIso (e : F ≅ 𝟭 C₁) :
    mapOfRingHom ψ hM F hF ≅ 𝟭 (Rationalization M₁ C₁) :=
  Localization.liftNatIso (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₁ C₁) (Q M₁ C₁) _ _
    (Functor.isoWhiskerRight e _ ≪≫ Functor.leftUnitor _)

lemma mapOfRingHomIdIso_hom_app (e : F ≅ 𝟭 C₁) (X : C₁) :
    (mapOfRingHomIdIso ψ hM F hF e).hom.app ((Q M₁ C₁).obj X) =
      (Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₁ C₁)
        (mapOfRingHom ψ hM F hF)).hom.app X ≫ (Q M₁ C₁).map (e.hom.app X) := by
  simp [mapOfRingHomIdIso, Localization.liftNatIso, Localization.liftNatTrans_app]
  rfl

end Id

end CategoryTheory.Rationalization
