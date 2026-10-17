/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassProduct

/-!
# The cup product of Thom classes

If `α` is a Thom class of `Z₁ ⊂ U` and the restriction of `β` to `Z₁` is a Thom class of
`Z ⊂ Z₁`, then the cup product with supports `α ∪ β` is a Thom class of `Z ⊂ U`
(`AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`). See
`WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassProduct` for the strategy.

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Transport

/-- If `ν : F ⟶ L ⋙ R` is an isomorphism and `L ⊣ R`, then postcomposition with `F.map χ` is
bijective on `Hom(S, F X)` as soon as postcomposition with `L.map χ` is bijective on
`Hom(L S, L X)`: the bijections `Hom(S, F X) ≅ Hom(S, R L X) ≅ Hom(L S, L X)` are natural. -/
lemma bijective_comp_map_of_adjunction {C D : Type*} [Category C] [Category D] {F : C ⥤ C}
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (ν : F ⟶ L ⋙ R) [IsIso ν] {S X Y : C} (χ : X ⟶ Y)
    (h : Function.Bijective (fun f : L.obj S ⟶ L.obj X ↦ f ≫ L.map χ)) :
    Function.Bijective (fun f : S ⟶ F.obj X ↦ f ≫ F.map χ) := by
  let Φ : ∀ T, (S ⟶ F.obj T) ≃ (L.obj S ⟶ L.obj T) := fun T ↦
    { toFun := fun f ↦ (adj.homEquiv _ _).symm (f ≫ ν.app T)
      invFun := fun g ↦ adj.homEquiv _ _ g ≫ inv (ν.app T)
      left_inv := fun f ↦ by simp
      right_inv := fun g ↦ by simp }
  have hΦ : ∀ f : S ⟶ F.obj X, Φ Y (f ≫ F.map χ) = Φ X f ≫ L.map χ := fun f ↦ by
    change (adj.homEquiv _ _).symm ((f ≫ F.map χ) ≫ ν.app Y) =
      (adj.homEquiv _ _).symm (f ≫ ν.app X) ≫ L.map χ
    rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, ν.naturality,
      Category.assoc]
    rfl
  have : (fun f : S ⟶ F.obj X ↦ f ≫ F.map χ) =
      (Φ Y).symm ∘ (fun f ↦ f ≫ L.map χ) ∘ Φ X := by
    funext f
    simp only [Function.comp_apply]
    rw [← hΦ, Equiv.symm_apply_apply]
  rw [this]
  exact (Φ Y).symm.bijective.comp (h.comp (Φ X).bijective)

variable [Finite Λ] {U Z₁ : Scheme.{u}} (i₁ : Z₁ ⟶ U) [IsClosedImmersion i₁]

/-- The projection formula for a closed immersion `i₁ : Z₁ ⟶ U`, as a natural transformation
`Ri₁_! Λ_{Z₁} ⊗ᴸ - ⟶ Ri₁_* Li₁^*`: the projection map, the left unitor and `Ri₁_! ≅ Ri₁_*`. -/
noncomputable def closedImmersionProjectionNatTrans :
    (derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁)) ⟶
      L((i₁)^*[ModuleCat.{u + 1} Λ]) ⋙ R((i₁)_*[ModuleCat.{u + 1} Λ]) :=
  (projectionMap (ModuleCat.{u + 1} Λ) i₁).app (constantComplex Λ Z₁) ≫
    Functor.whiskerLeft L((i₁)^*[ModuleCat.{u + 1} Λ])
      (Functor.whiskerRight (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) Z₁).hom
        R(i₁)_![ModuleCat.{u + 1} Λ]) ≫
    Functor.whiskerLeft L((i₁)^*[ModuleCat.{u + 1} Λ])
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i₁).hom

instance : IsIso (closedImmersionProjectionNatTrans Λ i₁) := by
  have := isIso_projectionMap_of_finite Λ i₁
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp only [closedImmersionProjectionNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

end Transport

section Product

variable [Finite Λ] {U Z₁ Z₂ Z : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]

/-- **The cup product of Thom classes.** Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` be closed immersions
meeting in `i : Z ⟶ U` (with `Z ⊆ Z₁` and `Z ⊆ Z₂` scheme-theoretically), `b : Z' ⟶ Z₁` the
base change of `i₂` along `i₁`, and let `α ∈ H_{Z₁}(U, L₁)`, `β ∈ H_{Z₂}(U, L₂)` be classes with
supports, `L₂` invertible. If the adjoint of `α` is an isomorphism and the adjoint of the
restriction of `β` to `Z₁` is an isomorphism, then the adjoint `Λ_Z ⟶ Ri^! (L₁ ⊗ L₂)` of the
cup product with supports `α ∪ β` is an isomorphism. -/
theorem isIso_supportedTranspose_cupWithSupports
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (b₁ : Z ⟶ Z₁) (hb₁ : b₁ ≫ i₁ = i) (b₂ : Z ⟶ Z₂) (hb₂ : b₂ ≫ i₂ = i)
    {Z' : Scheme.{u}} (b : Z' ⟶ Z₁) [IsClosedImmersion b] (g : Z' ⟶ Z₂)
    (hg : IsPullback g b i₂ i₁)
    {L₁ L₂ : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL₂ : DerivedCategory.isInvertible Λ U L₂)
    {L₂' : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj L₂ ≅ L₂')
    (Δ : constantComplex Λ U ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      (constantComplex Λ U)).obj (constantComplex Λ U)) [IsIso Δ]
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![ModuleCat.{u + 1} Λ]).obj L₁))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![ModuleCat.{u + 1} Λ]).obj L₂))
    (hα : IsIso (supportedTranspose Λ i₁ α))
    (hβ : IsIso (supportedTranspose Λ b (restrictSupportedClass (ModuleCat.{u + 1} Λ) i₁ i₂ b g
      hg (leftDerivedUpperStarConstantComplexIso Λ i₁).inv τ β))) :
    IsIso (supportedTranspose Λ i (cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β)) := by
  set u₁ := supportedRestrictionMap Λ i₁
  set u₂ := supportedRestrictionMap Λ i₂
  set φ₁ := supportedTranspose Λ i₁ α
  set φ₂ := supportedTranspose Λ i₂ β
  set χ₁ := (R(i₁)_![ModuleCat.{u + 1} Λ]).map φ₁ ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₁).counit.app L₁
  set χ₂ := (R(i₂)_![ModuleCat.{u + 1} Λ]).map φ₂ ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₂).counit.app L₂
  set Q := derivedTensorHom (ModuleCat.{u + 1} Λ) ((R(i₁)_![ModuleCat.{u + 1} Λ]).map φ₁)
      ((R(i₂)_![ModuleCat.{u + 1} Λ]).map φ₂) ≫
    supportedProduct (ModuleCat.{u + 1} Λ) i₁ i₂ i h L₁ L₂
  set w := Δ ≫ derivedTensorHom (ModuleCat.{u + 1} Λ) u₁ u₂
  have hα' : u₁ ≫ (R(i₁)_![ModuleCat.{u + 1} Λ]).map φ₁ = α :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i₁ α
  have hβ' : u₂ ≫ (R(i₂)_![ModuleCat.{u + 1} Λ]).map φ₂ = β :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i₂ β
  have hcup : cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β = w ≫ Q := by
    rw [cupWithSupports_eq, ← hα', ← hβ', ← derivedTensorHom_comp]
    simp only [w, Q, Category.assoc]
  have hsub₁ : Set.range i.base ⊆ Set.range i₁.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨b₁.base z, by rw [← Scheme.Hom.comp_apply, hb₁]⟩
  -- the source `E₁ ⊗ E₂` of `Q` is supported on `Z`
  have hT : IsSupported Λ i (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
        ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂))) :=
    isZero_leftDerivedUpperStar_derivedTensor_of_disjoint _ i₁ i₂ i h
      (fun v hv ↦ isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i₁ _ v hv)
      (fun v hv ↦ isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i₂ _ v hv)
      _ (disjoint_range_openComplement_ι i)
  -- `Λ_U ⟶ Ri_! Λ_Z` and `Λ_U ⟶ E₁ ⊗ E₂` are reflections, so they differ by an isomorphism
  have hLw : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map w) := by
    have hu : ∀ {Y : Scheme.{u}} (c : Y ⟶ U) [IsClosedImmersion c] (d : Z ⟶ Y),
        d ≫ c = i → IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ c)) := by
      intro Y c _ d hd
      have := isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ c
      have : IsIso ((L((c)^*[ModuleCat.{u + 1} Λ]) ⋙ L((d)^*[ModuleCat.{u + 1} Λ])).map
          (supportedRestrictionMap Λ c)) :=
        inferInstanceAs (IsIso ((L((d)^*[ModuleCat.{u + 1} Λ])).map
          ((L((c)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ c))))
      exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp _ d c i hd.symm) _).2 this
    have hu₁ := hu i₁ b₁ hb₁
    have hu₂ := hu i₂ b₂ hb₂
    have : IsIso (derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((L((i)^*[ModuleCat.{u + 1} Λ])).map u₁) ((L((i)^*[ModuleCat.{u + 1} Λ])).map u₂)) := by
      unfold derivedTensorHom
      infer_instance
    have hn := leftDerivedUpperStarTensorIso_hom_naturality (ModuleCat.{u + 1} Λ) i u₁ u₂
    have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorHom (ModuleCat.{u + 1} Λ) u₁ u₂) ≫
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) i _ _).hom) := by
      rw [hn]
      infer_instance
    have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorHom (ModuleCat.{u + 1} Λ) u₁ u₂)) :=
      IsIso.of_isIso_comp_right _ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) i _ _).hom
    simp only [w, Functor.map_comp]
    infer_instance
  obtain ⟨a, ha⟩ := exists_iso_comp_eq Λ i (isSupported_rightDerivedLowerShriek Λ i _) hT
    (supportedRestrictionMap Λ i) w (isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ i)
    hLw
  -- `Ri_! ψ = a ≫ Q`
  have hψ : (R(i)_![ModuleCat.{u + 1} Λ]).map
      (supportedTranspose Λ i (cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β)) =
        a.hom ≫ Q := by
    apply (bijective_supportedRestrictionMap_comp Λ i _).1
    dsimp only
    rw [supportedRestrictionMap_comp_map_supportedTranspose, ← Category.assoc, ha, hcup]
  suffices hQ : IsIso Q by
    have : IsIso ((R(i)_![ModuleCat.{u + 1} Λ]).map
        (supportedTranspose Λ i (cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β))) := by
      rw [hψ]
      infer_instance
    exact isIso_of_reflects_iso _ (R(i)_![ModuleCat.{u + 1} Λ])
  -- the composite of `Q` with the counit is `χ₁ ⊗ χ₂`
  have hQε : Q ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app
      (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj L₁).obj L₂) =
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).map χ₂ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).map χ₁).app L₂ := by
    have : Q ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj L₁).obj L₂) =
        derivedTensorHom (ModuleCat.{u + 1} Λ) χ₁ χ₂ := by
      simp only [Q, χ₁, χ₂, Category.assoc, supportedProduct_comp_counit, derivedTensorHom_comp]
    rw [this]
    exact (((derivedTensor (ModuleCat.{u + 1} Λ) U).map χ₁).naturality χ₂).symm
  -- `- ⊗ L₂` and the universal property of `χ₁`
  have h₁ : ∀ S, IsSupported Λ i S → Function.Bijective
      (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj L₂ ↦
          f ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).map χ₁).app L₂) := by
    obtain ⟨M, ⟨eM⟩, ⟨eM'⟩⟩ := hL₂
    have huniv₁ := (isIso_iff_isSupportedUniversal Λ i₁ φ₁).1 hα
    intro S hS
    exact bijective_comp_derivedTensor_map_app _ eM eM' χ₁
      (huniv₁ _ ((hS.derivedTensor M).mono hsub₁))
  -- the projection formula for `i₁` and the universal property of the restriction of `χ₂`
  have h₂ : ∀ S, IsSupported Λ i S → Function.Bijective
      (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
        f ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).map χ₂) := by
    intro S hS
    obtain ⟨σ, hσ⟩ := exists_iso_forget_restrictSupportedClass Λ i₁ i₂ b g hg τ β
    have huniv₂ := (isIso_iff_isSupportedUniversal Λ b _).1 hβ
    -- `L i₁^* S` is supported on `Z'`
    have hS' : IsSupported Λ b ((L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S) := by
      refine hS.leftDerivedUpperStar i₁ ?_
      rw [Set.disjoint_left]
      rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
      apply y.2
      rw [Scheme.range_snd_of_isPullback hg]
      refine ⟨b₂.base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hb₂, hz, Scheme.Hom.comp_apply]
      rfl
    have hχ₂ : Function.Bijective
        (fun f : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S ⟶ (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
          f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂) := by
      have h0 := huniv₂ _ hS'
      simp only [hσ] at h0
      have : (fun f : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S ⟶
            (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
              ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
            f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂) =
          (fun f ↦ f ≫ τ.inv) ∘
            (fun f ↦ f ≫ σ.hom ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂ ≫ τ.hom) ∘
              (fun f ↦ f ≫ σ.inv) := by
        funext f
        simp
      rw [this]
      exact (bijective_comp_right_of_isIso _).comp (h0.comp (bijective_comp_right_of_isIso _))
    -- transport along the projection formula and the adjunction `Li₁^* ⊣ Ri₁_*`
    exact bijective_comp_map_of_adjunction (derivedUpperStarLowerStarAdjunction _ i₁)
      (closedImmersionProjectionNatTrans Λ i₁) χ₂ hχ₂
  have hbQ : ∀ S, IsSupported Λ i S → Function.Bijective
      (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦ f ≫ Q) :=
    fun S hS ↦ by
      have h := bijective_comp_comp (h₂ S hS) (h₁ S hS)
      rw [← hQε] at h
      exact bijective_comp_of_bijective_comp_comp h (bijective_comp_counit Λ i hS _)
  exact isIso_of_bijective_comp_right _ (hbQ _ (isSupported_rightDerivedLowerShriek Λ i _)).2
    (hbQ _ hT).1

end Product

end Etale

end AlgebraicGeometry
