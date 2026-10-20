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

section Tensor

variable {A} {X : Scheme.{u}}

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

/-- A section `δ : Λ_X ⟶ Λ_X ⊗ Λ_X` of the left unitor is coassociative: it is the inverse of
the left unitor, and `λ⁻¹ ≫ (λ⁻¹ ⊗ 1) ≫ α = λ⁻¹ ≫ (1 ⊗ λ⁻¹)` by the triangle identity. -/
lemma coassoc_of_comp_derivedTensorLeftUnitor_hom
    (δ : (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))) ⟶
      ((derivedTensor A X).obj (𝟙_ _)).obj (𝟙_ _))
    (hδ : δ ≫ (derivedTensorLeftUnitor A X _).hom = 𝟙 _) :
    δ ≫ derivedTensorHom A δ (𝟙 _) ≫ (derivedTensorAssociator A X _ _ _).hom =
      δ ≫ derivedTensorHom A (𝟙 _) δ := by
  have : δ = (λ_ _).inv := (Iso.comp_hom_eq_id _).1 hδ
  subst this
  simp only [derivedTensorHom_eq_tensorHom, derivedTensorAssociator_eq]
  monoidal

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
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K₁ K₂ : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (hK₁ : ∀ {V : Scheme.{u}} (v : V ⟶ U), Disjoint (Set.range v.base) (Set.range i₁.base) →
      IsZero ((L((v)^*[A])).obj K₁))
    (hK₂ : ∀ {V : Scheme.{u}} (v : V ⟶ U), Disjoint (Set.range v.base) (Set.range i₂.base) →
      IsZero ((L((v)^*[A])).obj K₂))
    (w : W ⟶ U) (hw : Disjoint (Set.range w.base) (Set.range i.base)) :
    IsZero ((L((w)^*[A])).obj (((derivedTensor A U).obj K₁).obj K₂)) := by
  set j := i.openComplement.ι
  have hd : ∀ {Y : Scheme.{u}} (c : Y ⟶ U) [IsClosedImmersion c], Disjoint
      (Set.range ((pullback.snd c j).openComplement.ι ≫ j).base) (Set.range c.base) := by
    intro Y c _
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ hx
    apply x.2
    rw [Scheme.Pullback.range_snd]
    simpa using hx
  have hj : IsZero ((L((j)^*[A])).obj (((derivedTensor A U).obj K₁).obj K₂)) := by
    have hcd : Disjoint (Set.range (pullback.snd i₁ j)) (Set.range (pullback.snd i₂ j)) := by
      rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
      intro x hx₁ hx₂
      apply x.2
      rw [h]
      exact ⟨hx₁, hx₂⟩
    refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint A (pullback.snd i₁ j)
      (pullback.snd i₂ j) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
      (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp A _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_left (hK₁ _ (hd i₁)) _).of_iso
        (leftDerivedUpperStarTensorIso A _ _ _)
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp A _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_right _ (hK₂ _ (hd i₂))).of_iso
        (leftDerivedUpperStarTensorIso A _ _ _)
  have hw' : Set.range w.base ⊆ Set.range j.base := by
    rw [← compl_compl (Set.range j.base), ← i.range_eq_compl_range_openComplement_ι]
    exact hw.subset_compl_right
  rw [← IsOpenImmersion.lift_fac j w hw']
  exact ((L((IsOpenImmersion.lift j w hw')^*[A])).map_isZero hj).of_iso
    ((leftDerivedUpperStarComp A _ j).app _)

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
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    supportedProduct A i₁ i₂ i h M N ≫
        (rightDerivedUpperShriekAdjunction A i).counit.app (((derivedTensor A U).obj M).obj N) =
      derivedTensorHom A ((rightDerivedUpperShriekAdjunction A i₁).counit.app M)
        ((rightDerivedUpperShriekAdjunction A i₂).counit.app N) :=
  (existsUnique_supportedProduct A i₁ i₂ i h M N).exists.choose_spec

/-- **Naturality of the product of supports** in the coefficients `M` and `N`. -/
theorem supportedProduct_naturality (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {M M' N N' : DerivedCategory (Sheaf U.smallEtaleTopology A)} (φ : M ⟶ M') (ψ : N ⟶ N') :
    derivedTensorHom A ((R(i₁)_![A]).map ((R(i₁)^![A]).map φ))
        ((R(i₂)_![A]).map ((R(i₂)^![A]).map ψ)) ≫ supportedProduct A i₁ i₂ i h M' N' =
      supportedProduct A i₁ i₂ i h M N ≫
        (R(i)_![A]).map ((R(i)^![A]).map (derivedTensorHom A φ ψ)) := by
  have hS := isZero_leftDerivedUpperStar_derivedTensor_of_disjoint A i₁ i₂ i h
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i₁ ((R(i₁)^![A]).obj M))
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i₂ ((R(i₂)^![A]).obj N))
    i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_right)
  refine (existsUnique_comp_counit_of_isZero A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hS _).unique ?_ rfl
  simp only [Category.assoc]
  erw [(rightDerivedUpperShriekAdjunction A i).counit.naturality (derivedTensorHom A φ ψ)]
  rw [Functor.id_map, supportedProduct_comp_counit, reassoc_of% supportedProduct_comp_counit,
    derivedTensorHom_comp, derivedTensorHom_comp]
  erw [(rightDerivedUpperShriekAdjunction A i₁).counit.naturality φ,
    (rightDerivedUpperShriekAdjunction A i₂).counit.naturality ψ]
  rfl

/-- **Associativity of the product of supports.** For closed immersions `i₁, i₂, i₃` into `U`
and `i₁₂, i₂₃, i` with ranges `Z₁ ∩ Z₂`, `Z₂ ∩ Z₃` and `Z₁ ∩ Z₂ ∩ Z₃`:

```
(R₁ ⊗ R₂) ⊗ R₃ ──P₁₂ ⊗ 1──▶ R₁₂ ⊗ R₃ ──P──▶ Ri_! Ri^! ((M ⊗ N) ⊗ P)
      │ α                                              │ α
      ▼                                                ▼
R₁ ⊗ (R₂ ⊗ R₃) ──1 ⊗ P₂₃──▶ R₁ ⊗ R₂₃ ──P──▶ Ri_! Ri^! (M ⊗ (N ⊗ P))
```

Both composites lift `((ε₁ ⊗ ε₂) ⊗ ε₃) ≫ α = α ≫ (ε₁ ⊗ (ε₂ ⊗ ε₃))` through the counit, and their
source is supported on `Z`. -/
theorem supportedProduct_assoc (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i₃ : Z₃ ⟶ U) (i₁₂ : Z₁₂ ⟶ U)
    (i₂₃ : Z₂₃ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i₃]
    [IsClosedImmersion i₁₂] [IsClosedImmersion i₂₃] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i₃)_![A]).IsLeftAdjoint]
    [(R(i₁₂)_![A]).IsLeftAdjoint] [(R(i₂₃)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i₁₂.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i₁₂.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i₂₃.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₃ i₂₃.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₃ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂₃ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h₁₂ : Set.range i₁₂.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h₂₃ : Set.range i₂₃.base = Set.range i₂.base ∩ Set.range i₃.base)
    (h : Set.range i.base = Set.range i₁₂.base ∩ Set.range i₃.base)
    (h' : Set.range i.base = Set.range i₁.base ∩ Set.range i₂₃.base)
    (M N P : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    derivedTensorHom A (supportedProduct A i₁ i₂ i₁₂ h₁₂ M N) (𝟙 _) ≫
        supportedProduct A i₁₂ i₃ i h _ P ≫
          (R(i)_![A]).map ((R(i)^![A]).map (derivedTensorAssociator A U M N P).hom) =
      (derivedTensorAssociator A U _ _ _).hom ≫
        derivedTensorHom A (𝟙 _) (supportedProduct A i₂ i₃ i₂₃ h₂₃ N P) ≫
          supportedProduct A i₁ i₂₃ i h' M _ := by
  have hS := isZero_leftDerivedUpperStar_derivedTensor_of_disjoint A i₁₂ i₃ i h
    (fun v hv ↦ isZero_leftDerivedUpperStar_derivedTensor_of_disjoint A i₁ i₂ i₁₂ h₁₂
      (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i₁ ((R(i₁)^![A]).obj M))
      (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i₂ ((R(i₂)^![A]).obj N))
      v hv)
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i₃ ((R(i₃)^![A]).obj P))
    i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_right)
  refine (existsUnique_comp_counit_of_isZero A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hS _).unique ?_ rfl
  simp only [Category.assoc]
  erw [(rightDerivedUpperShriekAdjunction A i).counit.naturality
    (derivedTensorAssociator A U M N P).hom]
  rw [reassoc_of% supportedProduct_comp_counit, supportedProduct_comp_counit,
    derivedTensorHom_comp_assoc, derivedTensorHom_comp, supportedProduct_comp_counit,
    supportedProduct_comp_counit, Category.id_comp, Category.id_comp]
  exact derivedTensorHom_derivedTensorHom_comp_derivedTensorAssociator_hom _ _ _

/-- **The unit law of the product of supports.** For a surjective closed immersion `i₁`, the
product with the class `u : Λ_U ⟶ Ri₁_! Ri₁^! M` supported everywhere lifting `φ : Λ_U ⟶ M` is
`Λ_U ⊗ Ri_! Ri^! N ≅ Ri_! Ri^! N ⟶ Ri_! Ri^! (M ⊗ N)`, through `N ≅ Λ_U ⊗ N ⟶ M ⊗ N`. -/
theorem supportedProduct_liftCounitOfRangeEqUniv (i₁ : Z₁ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i i.openComplement.ι)_![A]).IsLeftAdjoint]
    (hi : Set.range i₁.base = Set.univ)
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i.base)
    {M : DerivedCategory (Sheaf U.smallEtaleTopology A)} (φ : 𝟙_ _ ⟶ M)
    (N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    derivedTensorHom A (liftCounitOfRangeEqUniv A i₁ hi φ) (𝟙 _) ≫
        supportedProduct A i₁ i i h M N =
      (derivedTensorLeftUnitor A U _).hom ≫ (R(i)_![A]).map ((R(i)^![A]).map
        ((derivedTensorLeftUnitor A U N).inv ≫ derivedTensorHom A φ (𝟙 N))) := by
  have hS := isZero_leftDerivedUpperStar_derivedTensor_of_disjoint A i₁ i i h
    (isZero_leftDerivedUpperStar_of_disjoint_of_range_eq_univ A i₁ hi
      (𝟙_ (DerivedCategory (Sheaf U.smallEtaleTopology A))))
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i ((R(i)^![A]).obj N))
    i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_right)
  refine (existsUnique_comp_counit_of_isZero A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι hS _).unique rfl ?_
  have hu : liftCounitOfRangeEqUniv A i₁ hi φ ≫
      (rightDerivedUpperShriekAdjunction A i₁).counit.app M = φ :=
    (existsUnique_comp_counit_of_range_eq_univ A i₁ hi φ).exists.choose_spec
  simp only [Category.assoc]
  erw [(rightDerivedUpperShriekAdjunction A i).counit.naturality]
  rw [Functor.id_map, supportedProduct_comp_counit, derivedTensorHom_comp,
    ← derivedTensorHom_id_comp_derivedTensorLeftUnitor_hom_assoc]
  erw [Iso.hom_inv_id_assoc]
  rw [derivedTensorHom_comp, hu]
  simp only [Category.id_comp]
  exact congrArg (derivedTensorHom A φ) (Category.comp_id _)

end Product

section Cup

variable {U Z₁ Z₂ Z₃ Z₁₂ Z₂₃ Z : Scheme.{u}}

/-- The cup product with supports, written with `AlgebraicGeometry.Etale.derivedTensorHom`. -/
lemma cupWithSupports_eq (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (Δ : K ⟶ ((derivedTensor A U).obj K).obj K)
    (α : K ⟶ (R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))
    (β : K ⟶ (R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) :
    cupWithSupports A i₁ i₂ i h Δ α β =
      Δ ≫ derivedTensorHom A α β ≫ supportedProduct A i₁ i₂ i h M N := by
  simp [cupWithSupports, derivedTensorHom]

/-- **Naturality of the cup product with supports** in the coefficients. -/
theorem cupWithSupports_comp_map (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K M M' N N' : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (Δ : K ⟶ ((derivedTensor A U).obj K).obj K)
    (α : K ⟶ (R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))
    (β : K ⟶ (R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) (φ : M ⟶ M') (ψ : N ⟶ N') :
    cupWithSupports A i₁ i₂ i h Δ α β ≫
        (R(i)_![A]).map ((R(i)^![A]).map (derivedTensorHom A φ ψ)) =
      cupWithSupports A i₁ i₂ i h Δ (α ≫ (R(i₁)_![A]).map ((R(i₁)^![A]).map φ))
        (β ≫ (R(i₂)_![A]).map ((R(i₂)^![A]).map ψ)) := by
  rw [cupWithSupports_eq, cupWithSupports_eq, Category.assoc, Category.assoc,
    ← supportedProduct_naturality, derivedTensorHom_comp_assoc]

/-- **Associativity of the cup product with supports**, for a coassociative diagonal
`Δ : K ⟶ K ⊗ K`:
`((α ∪ β) ∪ γ) ≫ α_{M,N,P} = α ∪ (β ∪ γ)`. -/
theorem cupWithSupports_assoc (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i₃ : Z₃ ⟶ U) (i₁₂ : Z₁₂ ⟶ U)
    (i₂₃ : Z₂₃ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i₃]
    [IsClosedImmersion i₁₂] [IsClosedImmersion i₂₃] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i₃)_![A]).IsLeftAdjoint]
    [(R(i₁₂)_![A]).IsLeftAdjoint] [(R(i₂₃)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i₁₂.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i₁₂.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i₂₃.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₃ i₂₃.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₃ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂₃ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h₁₂ : Set.range i₁₂.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h₂₃ : Set.range i₂₃.base = Set.range i₂.base ∩ Set.range i₃.base)
    (h : Set.range i.base = Set.range i₁₂.base ∩ Set.range i₃.base)
    (h' : Set.range i.base = Set.range i₁.base ∩ Set.range i₂₃.base)
    {K M N P : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (Δ : K ⟶ ((derivedTensor A U).obj K).obj K)
    (hΔ : Δ ≫ derivedTensorHom A Δ (𝟙 K) ≫ (derivedTensorAssociator A U K K K).hom =
      Δ ≫ derivedTensorHom A (𝟙 K) Δ)
    (α : K ⟶ (R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))
    (β : K ⟶ (R(i₂)_![A]).obj ((R(i₂)^![A]).obj N))
    (γ : K ⟶ (R(i₃)_![A]).obj ((R(i₃)^![A]).obj P)) :
    cupWithSupports A i₁₂ i₃ i h Δ (cupWithSupports A i₁ i₂ i₁₂ h₁₂ Δ α β) γ ≫
        (R(i)_![A]).map ((R(i)^![A]).map (derivedTensorAssociator A U M N P).hom) =
      cupWithSupports A i₁ i₂₃ i h' Δ α (cupWithSupports A i₂ i₃ i₂₃ h₂₃ Δ β γ) := by
  simp only [cupWithSupports_eq, Category.assoc]
  have e₁ : derivedTensorHom A (Δ ≫ derivedTensorHom A α β ≫ supportedProduct A i₁ i₂ i₁₂ h₁₂ M N)
      γ = derivedTensorHom A Δ (𝟙 K) ≫ derivedTensorHom A (derivedTensorHom A α β) γ ≫
        derivedTensorHom A (supportedProduct A i₁ i₂ i₁₂ h₁₂ M N) (𝟙 _) := by
    rw [derivedTensorHom_comp, derivedTensorHom_comp, Category.id_comp, Category.comp_id]
  have e₂ : derivedTensorHom A α (Δ ≫ derivedTensorHom A β γ ≫ supportedProduct A i₂ i₃ i₂₃ h₂₃ N P)
      = derivedTensorHom A (𝟙 K) Δ ≫ derivedTensorHom A α (derivedTensorHom A β γ) ≫
        derivedTensorHom A (𝟙 _) (supportedProduct A i₂ i₃ i₂₃ h₂₃ N P) := by
    rw [derivedTensorHom_comp, derivedTensorHom_comp, Category.id_comp, Category.comp_id]
  rw [e₁, e₂, Category.assoc, Category.assoc, supportedProduct_assoc A i₁ i₂ i₃ i₁₂ i₂₃ i h₁₂ h₂₃ h
    h', derivedTensorHom_derivedTensorHom_comp_derivedTensorAssociator_hom_assoc,
    reassoc_of% hΔ]
  simp only [Category.assoc]

/-- **The unit law of the cup product with supports.** For a surjective closed immersion `i₁`, a
section `Δ` of the left unitor of `Λ_U` and the class `u` supported everywhere lifting
`φ : Λ_U ⟶ M`, the cup product `u ∪ β` is `β` followed by `N ≅ Λ_U ⊗ N ⟶ M ⊗ N`. -/
theorem cupWithSupports_liftCounitOfRangeEqUniv (i₁ : Z₁ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i i.openComplement.ι)_![A]).IsLeftAdjoint]
    (hi : Set.range i₁.base = Set.univ)
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i.base)
    {M N : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (Δ : 𝟙_ _ ⟶ ((derivedTensor A U).obj (𝟙_ _)).obj (𝟙_ _))
    (hΔ : Δ ≫ (derivedTensorLeftUnitor A U _).hom = 𝟙 _) (φ : 𝟙_ _ ⟶ M)
    (β : 𝟙_ _ ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj N)) :
    cupWithSupports A i₁ i i h Δ (liftCounitOfRangeEqUniv A i₁ hi φ) β =
      β ≫ (R(i)_![A]).map ((R(i)^![A]).map
        ((derivedTensorLeftUnitor A U N).inv ≫ derivedTensorHom A φ (𝟙 N))) := by
  have e : derivedTensorHom A (liftCounitOfRangeEqUniv A i₁ hi φ) β =
      derivedTensorHom A (𝟙 _) β ≫
        derivedTensorHom A (liftCounitOfRangeEqUniv A i₁ hi φ) (𝟙 _) := by
    rw [derivedTensorHom_comp, Category.id_comp, Category.comp_id]
  rw [cupWithSupports_eq, e, Category.assoc, supportedProduct_liftCounitOfRangeEqUniv,
    reassoc_of% derivedTensorHom_id_comp_derivedTensorLeftUnitor_hom, reassoc_of% hΔ]

end Cup

end Etale

end AlgebraicGeometry
