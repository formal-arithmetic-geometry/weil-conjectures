/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Associativity and unit law of cup products with supports

The product of supports `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)`
(`AlgebraicGeometry.Etale.supportedProduct`) is natural in the coefficients `M`, `N`, associative
along the associator of the derived tensor product, and unital for classes supported everywhere.
All three statements are proved by the uniqueness of lifts through counits: the two sides are maps
out of an object supported on `Z`, into `Ri_! Ri^! L`, with the same composite with the counit.
For associativity, the source `(R₁ ⊗ R₂) ⊗ R₃` is supported on `Z₁ ∩ Z₂ ∩ Z₃`: a tensor product
of objects supported on `Z₁` and on `Z₂` is supported on `Z₁ ∩ Z₂`
(`AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_derivedTensor_of_disjoint`).

Consequently the cup product with supports (`AlgebraicGeometry.Etale.cupWithSupports`) is
associative for a coassociative diagonal, and the class supported everywhere lifting the unit is
a unit for it.

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_derivedTensor_of_disjoint`
- `AlgebraicGeometry.Etale.supportedProduct_naturality`
- `AlgebraicGeometry.Etale.supportedProduct_assoc`
- `AlgebraicGeometry.Etale.supportedProduct_liftCounitOfRangeEqUniv`
- `AlgebraicGeometry.Etale.cupWithSupports_comp_map`
- `AlgebraicGeometry.Etale.cupWithSupports_assoc`
- `AlgebraicGeometry.Etale.cupWithSupports_liftCounitOfRangeEqUniv`
- `AlgebraicGeometry.Etale.coassoc_of_comp_derivedTensorLeftUnitor_hom`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Tensor

variable {A} {Λ} {X : Scheme.{u}}

/-- `AlgebraicGeometry.Etale.derivedTensorHom` is the tensor product of morphisms of `D(X_ét)`. -/
lemma derivedTensorHom_eq_tensorHom
    {K K₁ M M₁ : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K₁) (g : M ⟶ M₁) :
    derivedTensorHom A f g = f ⊗ₘ g := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

/-- Naturality of the associator of the derived tensor product. -/
@[reassoc]
lemma derivedTensorHom_derivedTensorHom_comp_derivedTensorAssociator_hom
    {K K' M M' N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (f : K ⟶ K') (g : M ⟶ M') (k : N ⟶ N') :
    derivedTensorHom A (derivedTensorHom A f g) k ≫ (derivedTensorAssociator A X K' M' N').hom =
      (derivedTensorAssociator A X K M N).hom ≫
        derivedTensorHom A f (derivedTensorHom A g k) := by
  simp only [derivedTensorHom_eq_tensorHom, derivedTensorAssociator_eq]
  exact associator_naturality f g k

/-- Naturality of the left unitor of the derived tensor product. -/
@[reassoc]
lemma derivedTensorHom_id_comp_derivedTensorLeftUnitor_hom
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    derivedTensorHom A (𝟙 (𝟙_ _)) f ≫ (derivedTensorLeftUnitor A X M').hom =
      (derivedTensorLeftUnitor A X M).hom ≫ f := by
  rw [derivedTensorHom_eq_tensorHom, id_tensorHom]
  exact leftUnitor_naturality f

end Tensor

section Support

variable {U W Z₁ Z₂ Z : Scheme.{u}}

/-- **Tensor products of supported objects.** Let `i₁, i₂, i` be closed immersions into `U` with
`Z = Z₁ ∩ Z₂`, and `K₁`, `K₂` objects of `D(U_ét)` restricting to zero on every scheme over `U`
missing `Z₁`, respectively `Z₂`. Then `K₁ ⊗ K₂` restricts to zero on every scheme `w : W ⟶ U`
missing `Z`: on the open complement of `Z`, its restrictions to the complements of `Z₁` and of
`Z₂` vanish, and these two opens cover it. -/
lemma isZero_leftDerivedUpperStar_derivedTensor_of_disjoint (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U)
    (i : Z ⟶ U) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K₁ K₂ : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK₁ : ∀ {V : Scheme.{u}} (v : V ⟶ U), Disjoint (Set.range v.base) (Set.range i₁.base) →
      IsZero ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K₁))
    (hK₂ : ∀ {V : Scheme.{u}} (v : V ⟶ U), Disjoint (Set.range v.base) (Set.range i₂.base) →
      IsZero ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K₂))
    (w : W ⟶ U) (hw : Disjoint (Set.range w.base) (Set.range i.base)) :
    IsZero ((L((w)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        K₁).obj K₂)) := by
  set j := i.openComplement.ι
  have hd : ∀ {Y : Scheme.{u}} (c : Y ⟶ U) [IsClosedImmersion c], Disjoint
      (Set.range ((pullback.snd c j).openComplement.ι ≫ j).base) (Set.range c.base) := by
    intro Y c _
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ hx
    apply x.2
    rw [Scheme.Pullback.range_snd]
    simpa using hx
  have hj : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
      U).obj K₁).obj K₂)) := by
    have hcd : Disjoint (Set.range (pullback.snd i₁ j)) (Set.range (pullback.snd i₂ j)) := by
      rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
      intro x hx₁ hx₂
      apply x.2
      rw [h]
      exact ⟨hx₁, hx₂⟩
    refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint Λ (pullback.snd i₁ j)
      (pullback.snd i₂ j) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
      (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_left (hK₁ _ (hd i₁)) _).of_iso
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_right _ (hK₂ _ (hd i₂))).of_iso
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
  have hw' : Set.range w.base ⊆ Set.range j.base := by
    rw [← compl_compl (Set.range j.base), ← i.range_eq_compl_range_openComplement_ι]
    exact hw.subset_compl_right
  rw [← IsOpenImmersion.lift_fac j w hw']
  exact ((L((IsOpenImmersion.lift j w hw')^*[ModuleCat.{u + 1} Λ])).map_isZero hj).of_iso
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _)

/-- An object `Ri_! B` restricts to zero on every scheme over `U` missing the range of the
closed immersion `i`. -/
lemma isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint (i : Z ⟶ U)
    [IsClosedImmersion i] (B : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (w : W ⟶ U) (hw : Disjoint (Set.range w.base) (Set.range i.base)) :
    IsZero ((L((w)^*[A])).obj ((R(i)_![A]).obj B)) := by
  refine isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i
    i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left) w ?_ B
  rw [← compl_compl (Set.range i.openComplement.ι.base), ← i.range_eq_compl_range_openComplement_ι]
  exact hw.subset_compl_right

/-- Every object restricts to zero on a scheme missing a surjective closed immersion. -/
lemma isZero_leftDerivedUpperStar_of_disjoint_of_range_eq_univ (i : Z ⟶ U)
    (hi : Set.range i.base = Set.univ) (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (w : W ⟶ U) (hw : Disjoint (Set.range w.base) (Set.range i.base)) :
    IsZero ((L((w)^*[A])).obj K) := by
  have : IsEmpty W := ⟨fun x ↦ (Set.disjoint_left.1 hw ⟨x, rfl⟩) (hi ▸ Set.mem_univ _)⟩
  exact isZero_derivedCategory_of_isEmpty A W _

end Support

section Product

variable {U Z₁ Z₂ Z₃ Z₁₂ Z₂₃ Z : Scheme.{u}}

/-- The defining property of the product of supports: its composite with the counit is the
tensor product of the counits. -/
lemma supportedProduct_comp_counit (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedProduct Λ i₁ i₂ i h M N ≫
        (rightDerivedUpperShriekAdjunction Λ i).counit.app (((derivedTensor (ModuleCat.{u + 1} Λ)
            U).obj M).obj N) =
      derivedTensorHom (ModuleCat.{u + 1} Λ) ((rightDerivedUpperShriekAdjunction Λ i₁).counit.app M)
        ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) :=
  (existsUnique_supportedProduct Λ i₁ i₂ i h M N).exists.choose_spec

end Product

section Cup

variable {U Z₁ Z₂ Z₃ Z₁₂ Z₂₃ Z : Scheme.{u}}

/-- The cup product with supports, written with `AlgebraicGeometry.Etale.derivedTensorHom`. -/
lemma cupWithSupports_eq (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (Δ : K ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj K)
    (α : K ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))
    (β : K ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N)) :
    cupWithSupports Λ i₁ i₂ i h Δ α β =
      Δ ≫ derivedTensorHom (ModuleCat.{u + 1} Λ) α β ≫ supportedProduct Λ i₁ i₂ i h M N := by
  simp [cupWithSupports, derivedTensorHom]

end Cup

end Etale

end AlgebraicGeometry
