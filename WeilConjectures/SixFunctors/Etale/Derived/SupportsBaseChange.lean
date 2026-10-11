/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Restriction of cup products with supports

The cup product with supports (`AlgebraicGeometry.Etale.cupWithSupports`) commutes with the
restriction of supports (`AlgebraicGeometry.Etale.restrictSupportedClass`) along any morphism
`e : U' ⟶ U`: restricting `α ∪ β` is the cup product of the restrictions of `α` and `β`, provided
the diagonals used to multiply the classes are compatible with the pullback.

Both sides are classes `K' ⟶ Ri'_! Ri'^! (M' ⊗ N')` built out of lifts through counits, and the
comparison reduces to the base change of the product of supports
(`AlgebraicGeometry.Etale.supportedProduct`): two maps out of an object supported on `Z'` into
`Ri'_! Ri'^! L'` agree as soon as their composites with the counit agree.

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_derivedTensor_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.supportedProduct_baseChange`
- `AlgebraicGeometry.Etale.restrictSupportedClass_cupWithSupports`
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

variable {U U' W Z₁ Z₂ Z Z₁' Z₂' Z' : Scheme.{u}}

/-- A tensor product `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N` restricts to zero along every `w : W ⟶ U`
missing `Z = Z₁ ∩ Z₂`: on the open complement of `Z`, its restrictions to the complements of
`Z₁` and of `Z₂` vanish, and these two opens cover it. -/
lemma isZero_leftDerivedUpperStar_derivedTensor_rightDerivedLowerShriek (i₁ : Z₁ ⟶ U)
    (i₂ : Z₂ ⟶ U) (i : Z ⟶ U) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A)) (w : W ⟶ U)
    (hw : Set.range w.base ⊆ Set.range i.openComplement.ι.base) :
    IsZero ((L((w)^*[A])).obj (((derivedTensor A U).obj
      ((R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))).obj ((R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)))) := by
  set j := i.openComplement.ι
  have hj : IsZero ((L((j)^*[A])).obj (((derivedTensor A U).obj
      ((R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))).obj
        ((R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)))) := by
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
      exact (isZero_derivedTensor_obj_obj_of_isZero_left
        (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek A i₁ j _)
          _).of_iso (leftDerivedUpperStarTensorIso A _ _ _)
    · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp A _ j).app _).symm
      exact (isZero_derivedTensor_obj_obj_of_isZero_right _
        (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek A i₂ j
          _)).of_iso (leftDerivedUpperStarTensorIso A _ _ _)
  rw [← IsOpenImmersion.lift_fac j w hw]
  exact ((L((IsOpenImmersion.lift j w hw)^*[A])).map_isZero hj).of_iso
    ((leftDerivedUpperStarComp A _ j).app _)

/-- The tensor product `f ⊗ g` of two morphisms of `D(X_ét)`. -/
noncomputable def derivedTensorHom {X : Scheme.{u}}
    {K K₁ M M₁ : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K₁) (g : M ⟶ M₁) :
    ((derivedTensor A X).obj K).obj M ⟶ ((derivedTensor A X).obj K₁).obj M₁ :=
  ((derivedTensor A X).map f).app M ≫ ((derivedTensor A X).obj K₁).map g

variable {A} in
/-- Composition of tensor products of morphisms. -/
@[reassoc]
lemma derivedTensorHom_comp {X : Scheme.{u}}
    {K K₁ K₂ M M₁ M₂ : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (f : K ⟶ K₁) (g : M ⟶ M₁) (f' : K₁ ⟶ K₂) (g' : M₁ ⟶ M₂) :
    derivedTensorHom A f g ≫ derivedTensorHom A f' g' = derivedTensorHom A (f ≫ f') (g ≫ g') := by
  simp only [derivedTensorHom, Category.assoc, Functor.map_comp, NatTrans.comp_app]
  rw [((derivedTensor A X).map f').naturality_assoc g]

variable (e : U' ⟶ U) [(e)^*[A].PreservesFlat]

/-- The comparison `Le^*(K ⊗ M) ≅ Le^* K ⊗ Le^* M` is natural in both variables. -/
@[reassoc]
lemma leftDerivedUpperStarTensorIso_hom_naturality
    {K K₁ M M₁ : DerivedCategory (Sheaf U.smallEtaleTopology A)} (f : K ⟶ K₁) (g : M ⟶ M₁) :
    (L((e)^*[A])).map (derivedTensorHom A f g) ≫ (leftDerivedUpperStarTensorIso A e K₁ M₁).hom =
      (leftDerivedUpperStarTensorIso A e K M).hom ≫
        derivedTensorHom A ((L((e)^*[A])).map f) ((L((e)^*[A])).map g) := by
  have h₁ := congr_app ((leftDerivedUpperStarTensorNatIso A e).hom.naturality f) M
  have h₂ := ((leftDerivedUpperStarTensorNatIso A e).hom.app K₁).naturality g
  simp only [NatTrans.comp_app] at h₁ h₂
  simp only [leftDerivedUpperStarTensorIso, Iso.app_hom, Functor.map_comp, Category.assoc,
    derivedTensorHom]
  erw [h₂]
  rw [← Category.assoc, ← Category.assoc]
  erw [h₁]
  rfl

/-- **Base change of the product of supports.** For closed immersions `i₁, i₂, i` into `U` with
`Z = Z₁ ∩ Z₂`, their base changes `i₁', i₂', i'` along `e : U' ⟶ U`, and identifications
`τ_M : Le^* M ≅ M'`, `τ_N : Le^* N ≅ N'`, the product of supports
(`AlgebraicGeometry.Etale.supportedProduct`) commutes with the restrictions of supports `ψ`:

```
Le^*(R₁ ⊗ R₂) ──Le^* P──▶ Le^* Ri_! Ri^! (M ⊗ N) ──ψ──▶ Ri'_! Ri'^! (M' ⊗ N')
      │ ≅                                                        ‖
      ▼                                                          ‖
Le^* R₁ ⊗ Le^* R₂ ────ψ₁ ⊗ ψ₂────▶ R₁' ⊗ R₂' ─────P'──────▶ Ri'_! Ri'^! (M' ⊗ N')
```

Both composites lift `Le^*(ε₁ ⊗ ε₂)` through the counit, and their source is supported on `Z'`.
-/
theorem supportedProduct_baseChange (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    (i₁' : Z₁' ⟶ U') (i₂' : Z₂' ⟶ U') (i' : Z' ⟶ U')
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂'] [IsClosedImmersion i']
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(i₁')_![A]).IsLeftAdjoint] [(R(i₂')_![A]).IsLeftAdjoint] [(R(i')_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁' i'.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂' i'.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range i'.base = Set.range i₁'.base ∩ Set.range i₂'.base)
    (g₁ : Z₁' ⟶ Z₁) (g₂ : Z₂' ⟶ Z₂) (g : Z' ⟶ Z) (hg₁ : IsPullback g₁ i₁' i₁ e)
    (hg₂ : IsPullback g₂ i₂' i₂ e) (hg : IsPullback g i' i e)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M' N' : DerivedCategory (Sheaf U'.smallEtaleTopology A))
    (τM : (L((e)^*[A])).obj M ≅ M') (τN : (L((e)^*[A])).obj N ≅ N') :
    (leftDerivedUpperStarTensorIso A e _ _).inv ≫
        (L((e)^*[A])).map (supportedProduct A i₁ i₂ i h M N) ≫
          supportedRestriction A e i i' g hg _ _
            (leftDerivedUpperStarTensorIso A e M N ≪≫
              ((derivedTensor A U').mapIso τM).app _ ≪≫ ((derivedTensor A U').obj M').mapIso τN) =
      derivedTensorHom A (supportedRestriction A e i₁ i₁' g₁ hg₁ M M' τM)
          (supportedRestriction A e i₂ i₂' g₂ hg₂ N N' τN) ≫
        supportedProduct A i₁' i₂' i' h' M' N' := by
  set j' := i'.openComplement.ι
  have hP := (existsUnique_supportedProduct A i₁ i₂ i h M N).exists.choose_spec
  have hP' := (existsUnique_supportedProduct A i₁' i₂' i' h' M' N').exists.choose_spec
  have hψ := (existsUnique_supportedRestriction A e i i' g hg _ _
    (leftDerivedUpperStarTensorIso A e M N ≪≫
      ((derivedTensor A U').mapIso τM).app _ ≪≫
        ((derivedTensor A U').obj M').mapIso τN)).exists.choose_spec
  have hψ₁ := (existsUnique_supportedRestriction A e i₁ i₁' g₁ hg₁ M M' τM).exists.choose_spec
  have hψ₂ := (existsUnique_supportedRestriction A e i₂ i₂' g₂ hg₂ N N' τN).exists.choose_spec
  -- the source is supported on `Z'`
  have hj' : Set.range (j' ≫ e).base ⊆ Set.range i.openComplement.ι.base := by
    rw [← compl_compl (Set.range i.openComplement.ι.base),
      ← i.range_eq_compl_range_openComplement_ι, Set.subset_compl_iff_disjoint_left,
      Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
    apply x.2
    rw [Scheme.range_snd_of_isPullback hg]
    exact ⟨z, hx.symm⟩
  have hS := (isZero_leftDerivedUpperStar_derivedTensor_rightDerivedLowerShriek A i₁ i₂ i h M N
    (j' ≫ e) hj').of_iso ((L((j')^*[A])).mapIso (leftDerivedUpperStarTensorIso A e _ _).symm ≪≫
      ((leftDerivedUpperStarComp A j' e).app _).symm)
  refine (existsUnique_comp_counit_of_isZero A i' j' i'.range_eq_compl_range_openComplement_ι hS
    _).unique ?_ rfl
  have hP₁ : supportedProduct A i₁ i₂ i h M N ≫
      (rightDerivedUpperShriekAdjunction A i).counit.app (((derivedTensor A U).obj M).obj N) =
        derivedTensorHom A ((rightDerivedUpperShriekAdjunction A i₁).counit.app M)
          ((rightDerivedUpperShriekAdjunction A i₂).counit.app N) := hP
  have hP₁' : supportedProduct A i₁' i₂' i' h' M' N' ≫
      (rightDerivedUpperShriekAdjunction A i').counit.app (((derivedTensor A U').obj M').obj N') =
        derivedTensorHom A ((rightDerivedUpperShriekAdjunction A i₁').counit.app M')
          ((rightDerivedUpperShriekAdjunction A i₂').counit.app N') := hP'
  have hτ : (leftDerivedUpperStarTensorIso A e M N ≪≫
      ((derivedTensor A U').mapIso τM).app _ ≪≫ ((derivedTensor A U').obj M').mapIso τN).hom =
        (leftDerivedUpperStarTensorIso A e M N).hom ≫ derivedTensorHom A τM.hom τN.hom := by
    simp [derivedTensorHom]
  simp only [Category.assoc]
  erw [hψ]
  rw [hP₁', derivedTensorHom_comp]
  erw [hψ₁, hψ₂]
  rw [← Functor.map_comp_assoc, hP₁, hτ,
    ]
  erw [leftDerivedUpperStarTensorIso_hom_naturality_assoc, Iso.inv_hom_id_assoc]
  rw [derivedTensorHom_comp]

/-- **Base change of the cup product with supports.** Restricting a cup product with supports
`α ∪ β` (`AlgebraicGeometry.Etale.cupWithSupports`) along `e : U' ⟶ U` gives the cup product of
the restrictions of `α` and `β` (`AlgebraicGeometry.Etale.restrictSupportedClass`), for diagonals
`Δ : K ⟶ K ⊗ K` and `Δ' : K' ⟶ K' ⊗ K'` compatible with the pullback along `σ : K' ⟶ Le^* K`. -/
theorem restrictSupportedClass_cupWithSupports (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    (i₁' : Z₁' ⟶ U') (i₂' : Z₂' ⟶ U') (i' : Z' ⟶ U')
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂'] [IsClosedImmersion i']
    [(R(i₁)_![A]).IsLeftAdjoint] [(R(i₂)_![A]).IsLeftAdjoint] [(R(i)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂ i.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(i₁')_![A]).IsLeftAdjoint] [(R(i₂')_![A]).IsLeftAdjoint] [(R(i')_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₁' i'.openComplement.ι)_![A]).IsLeftAdjoint]
    [(R(pullback.snd i₂' i'.openComplement.ι)_![A]).IsLeftAdjoint]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range i'.base = Set.range i₁'.base ∩ Set.range i₂'.base)
    (g₁ : Z₁' ⟶ Z₁) (g₂ : Z₂' ⟶ Z₂) (g : Z' ⟶ Z) (hg₁ : IsPullback g₁ i₁' i₁ e)
    (hg₂ : IsPullback g₂ i₂' i₂ e) (hg : IsPullback g i' i e)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    {K' M' N' : DerivedCategory (Sheaf U'.smallEtaleTopology A)}
    (σ : K' ⟶ (L((e)^*[A])).obj K)
    (τM : (L((e)^*[A])).obj M ≅ M') (τN : (L((e)^*[A])).obj N ≅ N')
    (Δ : K ⟶ ((derivedTensor A U).obj K).obj K) (Δ' : K' ⟶ ((derivedTensor A U').obj K').obj K')
    (hΔ : Δ' ≫ derivedTensorHom A σ σ =
      σ ≫ (L((e)^*[A])).map Δ ≫ (leftDerivedUpperStarTensorIso A e K K).hom)
    (α : K ⟶ (R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))
    (β : K ⟶ (R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) :
    restrictSupportedClass A e i i' g hg σ
        (leftDerivedUpperStarTensorIso A e M N ≪≫
          ((derivedTensor A U').mapIso τM).app _ ≪≫ ((derivedTensor A U').obj M').mapIso τN)
        (cupWithSupports A i₁ i₂ i h Δ α β) =
      cupWithSupports A i₁' i₂' i' h' Δ' (restrictSupportedClass A e i₁ i₁' g₁ hg₁ σ τM α)
        (restrictSupportedClass A e i₂ i₂' g₂ hg₂ σ τN β) := by
  have hc : ∀ {X : Scheme.{u}} {Y₁ Y₂ Y : Scheme.{u}} (j₁ : Y₁ ⟶ X) (j₂ : Y₂ ⟶ X) (j : Y ⟶ X)
      [IsClosedImmersion j₁] [IsClosedImmersion j₂] [IsClosedImmersion j]
      [(R(j₁)_![A]).IsLeftAdjoint] [(R(j₂)_![A]).IsLeftAdjoint] [(R(j)_![A]).IsLeftAdjoint]
      [(R(pullback.snd j₁ j.openComplement.ι)_![A]).IsLeftAdjoint]
      [(R(pullback.snd j₂ j.openComplement.ι)_![A]).IsLeftAdjoint]
      (hj : Set.range j.base = Set.range j₁.base ∩ Set.range j₂.base)
      {K M N : DerivedCategory (Sheaf X.smallEtaleTopology A)}
      (Δ : K ⟶ ((derivedTensor A X).obj K).obj K)
      (α : K ⟶ (R(j₁)_![A]).obj ((R(j₁)^![A]).obj M))
      (β : K ⟶ (R(j₂)_![A]).obj ((R(j₂)^![A]).obj N)),
      cupWithSupports A j₁ j₂ j hj Δ α β =
        Δ ≫ derivedTensorHom A α β ≫ supportedProduct A j₁ j₂ j hj M N := by
    intros
    simp [cupWithSupports, derivedTensorHom]
  have key : (L((e)^*[A])).map (derivedTensorHom A α β) =
      (leftDerivedUpperStarTensorIso A e K K).hom ≫
        derivedTensorHom A ((L((e)^*[A])).map α) ((L((e)^*[A])).map β) ≫
          (leftDerivedUpperStarTensorIso A e _ _).inv := by
    rw [← cancel_mono (leftDerivedUpperStarTensorIso A e _ _).hom, Category.assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id,
      leftDerivedUpperStarTensorIso_hom_naturality]
  have hP := supportedProduct_baseChange A e i₁ i₂ i i₁' i₂' i' h h' g₁ g₂ g hg₁ hg₂ hg M N M' N'
    τM τN
  rw [hc, hc]
  simp only [restrictSupportedClass, Functor.map_comp, Category.assoc]
  rw [key]
  simp only [Category.assoc]
  rw [hP, ← reassoc_of% hΔ, derivedTensorHom_comp_assoc, derivedTensorHom_comp_assoc]
  simp only [Category.assoc]

omit [(e)^*[A].PreservesFlat] in
/-- **Naturality of the restriction of supports in the coefficients.** For `φ : L₁ ⟶ L₂` on `U`
and `φ' : L₁' ⟶ L₂'` on `U'` compatible with identifications `τ₁ : Le^* L₁ ≅ L₁'` and
`τ₂ : Le^* L₂ ≅ L₂'`, restricting `γ ≫ Ri_! Ri^! φ` gives the restriction of `γ` followed by
`Ri'_! Ri'^! φ'`. -/
theorem restrictSupportedClass_map (i : Z ⟶ U) (i' : Z' ⟶ U') [IsClosedImmersion i]
    [(R(i)_![A]).IsLeftAdjoint] [IsClosedImmersion i'] [(R(i')_![A]).IsLeftAdjoint]
    (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {K L₁ L₂ : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    {K' L₁' L₂' : DerivedCategory (Sheaf U'.smallEtaleTopology A)}
    (σ : K' ⟶ (L((e)^*[A])).obj K) (τ₁ : (L((e)^*[A])).obj L₁ ≅ L₁')
    (τ₂ : (L((e)^*[A])).obj L₂ ≅ L₂') (φ : L₁ ⟶ L₂) (φ' : L₁' ⟶ L₂')
    (hφ : (L((e)^*[A])).map φ ≫ τ₂.hom = τ₁.hom ≫ φ')
    (γ : K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj L₁)) :
    restrictSupportedClass A e i i' g hg σ τ₂ (γ ≫ (R(i)_![A]).map ((R(i)^![A]).map φ)) =
      restrictSupportedClass A e i i' g hg σ τ₁ γ ≫ (R(i')_![A]).map ((R(i')^![A]).map φ') := by
  have hψ₁ := (existsUnique_supportedRestriction A e i i' g hg L₁ L₁' τ₁).exists.choose_spec
  have hψ₂ := (existsUnique_supportedRestriction A e i i' g hg L₂ L₂' τ₂).exists.choose_spec
  have hS : IsZero ((L((i'.openComplement.ι)^*[A])).obj
      ((L((e)^*[A])).obj ((R(i)_![A]).obj ((R(i)^![A]).obj L₁)))) := by
    have hk : Set.range (i'.openComplement.ι ≫ e).base ⊆ Set.range i.openComplement.ι.base := by
      rw [← compl_compl (Set.range i.openComplement.ι.base),
        ← i.range_eq_compl_range_openComplement_ι, Set.subset_compl_iff_disjoint_left,
        Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
      apply x.2
      rw [Scheme.range_snd_of_isPullback hg]
      exact ⟨z, hx.symm⟩
    have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
      rw [i.range_eq_compl_range_openComplement_ι]
      exact disjoint_compl_left
    exact (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i
      i.openComplement.ι hdisj _ hk _).of_iso
        ((leftDerivedUpperStarComp A i'.openComplement.ι e).app _).symm
  have key : (L((e)^*[A])).map ((R(i)_![A]).map ((R(i)^![A]).map φ)) ≫
      supportedRestriction A e i i' g hg L₂ L₂' τ₂ =
        supportedRestriction A e i i' g hg L₁ L₁' τ₁ ≫
          (R(i')_![A]).map ((R(i')^![A]).map φ') := by
    refine (existsUnique_comp_counit_of_isZero A i' i'.openComplement.ι
      i'.range_eq_compl_range_openComplement_ι hS _).unique rfl ?_
    simp only [Category.assoc]
    erw [(rightDerivedUpperShriekAdjunction A i').counit.naturality φ', reassoc_of% hψ₁, hψ₂]
    rw [← Functor.map_comp_assoc]
    erw [(rightDerivedUpperShriekAdjunction A i).counit.naturality φ]
    rw [Functor.map_comp_assoc]
    erw [hφ]
    rfl
  simp only [restrictSupportedClass, Functor.map_comp, Category.assoc, key]

end Etale

end AlgebraicGeometry
