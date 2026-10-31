/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ReductionLowerShriekFormal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReduction
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The reduction of coefficients commutes with proper direct images

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars, left adjoint to the restriction of scalars `Res`.
For a morphism `g : Z ⟶ Y`, the comparison `β_g : Ψ_Y ∘ Rg_* ⟶ Rg_* ∘ Ψ_Z`
(`AlgebraicGeometry.Etale.derivedExtendScalarsLowerStarComparison`) is the mate of the
commutation of `Ψ` with the derived pullback.

Suppose given identifications `θ_X : K ⊗ᴸ R_X ≅ Res Ψ K` of `Res ∘ Ψ` with the tensor product with
an object `R_X` (in practice `Res Λ'_X`), compatible with `Lg^*` (`hθ`). Then `Res β_g` is, up to
`θ`, the projection map `Rg_* M ⊗ᴸ R_Y ⟶ Rg_*(M ⊗ᴸ Lg^* R_Y)`; for `g` proper the projection
formula holds at finite coefficients, hence `β_g` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedExtendScalarsLowerStarComparison`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The derived restriction of scalars reflects isomorphisms: so does the restriction of scalars of
sheaves, and isomorphisms of the derived categories are detected on cohomology sheaves. -/
instance reflectsIsomorphisms_derivedRestrictScalars {R S : Type (u + 1)} [CommRing R]
    [CommRing S] (T : Scheme.{u}) (φ : R →+* S) :
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).ReflectsIsomorphisms where
  reflects {K L} e he := by
    let F := Sheaf.restrictScalars T.smallEtaleTopology φ
    rw [DerivedCategory.isIso_iff] at he ⊢
    intro n
    have hm : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map e)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) e).2 (he n)
    exact isIso_of_reflects_iso _ F

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Comparison

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The comparison `β_g : Ψ_Y (Rg_* M) ⟶ Rg_* (Ψ_Z M)` of the derived extension of scalars with the
derived direct image: the mate of the commutation `Lg^* ⋙ Ψ_Z ≅ Ψ_Y ⋙ Lg^*`. -/
noncomputable def derivedExtendScalarsLowerStarComparison :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha Y ⟶
      derivedExtendScalars hρ ha Z ⋙ R((g)_*[ModuleCat.{u + 1} Λ']) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (TwoSquare.mk _ _ _ _ (derivedExtendScalarsPullbackIso hρ ha g).inv)).natTrans

/-- The comparison `Res_Y (Rg_* N) ⟶ Rg_* (Res_Z N)` of the restriction of scalars with the derived
direct image: the mate of the commutation of `Res` with `Lg^*`. -/
noncomputable def derivedRestrictScalarsLowerStarComparison :
    R((g)_*[ModuleCat.{u + 1} Λ']) ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ ⟶
      Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ ⋙ R((g)_*[ModuleCat.{u + 1} Λ]) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (leftDerivedUpperStarRestrictScalarsIso ρ g).hom).natTrans

/-- The comparison of `Res` with `Rg_*` is the inverse of the commutation
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso` when `g` has bounded
cohomological dimension, hence an isomorphism. -/
lemma isIso_derivedRestrictScalarsLowerStarComparison (d : ℕ)
    (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    IsIso (derivedRestrictScalarsLowerStarComparison g (ρ := ρ)) := by
  have h := mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso
    ρ g d hd
  rw [derivedRestrictScalarsLowerStarComparison, h]
  infer_instance

/-- The transpose along `Lg^* ⊣ Rg_*` of `Res Ψ (ε_M) ∘ (Lg^* Res Ψ ≅ Res Ψ Lg^*)` is
`Res β_g` followed by the comparison of `Res` with `Rg_*`. -/
lemma homEquiv_comp_map_counit_eq (M : 𝐃(Z, Λ)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _
        ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app _ ≫
          (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).map
            ((derivedExtendScalarsPullbackIso hρ ha g).inv.app _ ≫
              (derivedExtendScalars hρ ha Z).map
                ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app M))) =
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
          ((derivedExtendScalarsLowerStarComparison hρ ha g).app M) ≫
        (derivedRestrictScalarsLowerStarComparison g (ρ := ρ)).app _ := by
  apply ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _).symm.injective
  have h₁ := mateEquiv_counit (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (leftDerivedUpperStarRestrictScalarsIso ρ g).hom ((derivedExtendScalars hρ ha Z).obj M)
  have h₂ := mateEquiv_counit (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (TwoSquare.mk _ _ _ _ (derivedExtendScalarsPullbackIso hρ ha g).inv) M
  have hι := (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.naturality
    ((derivedExtendScalarsLowerStarComparison hρ ha g).app M)
  dsimp at h₁ h₂ hι
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
    Functor.map_comp]
  erw [h₁]
  rw [reassoc_of% hι, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact h₂.symm

/-- The square `Lg^*(K ⊗ᴸ R_Y) ⟶ Lg^* K ⊗ᴸ Lg^* R_Y ≅ Lg^* K ⊗ᴸ R_Z` of the tensor products with
`R_Y` and `R_Z`, for an identification `c : Lg^* R_Y ≅ R_Z`. -/
@[simps]
noncomputable def tensorPullbackSquare (R_Y : 𝐃(Y, Λ)) (R_Z : 𝐃(Z, Λ))
    (c : (L((g)^*[ModuleCat.{u + 1} Λ])).obj R_Y ≅ R_Z) :
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj R_Y ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) Z).flip.obj R_Z where
  app K := ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) g).app K).app R_Y ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)).map c.hom
  naturality K K' f := by
    have h := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison _ g).naturality f) R_Y
    have h' := ((derivedTensor (ModuleCat.{u + 1} Λ) Z).map
      (L((g)^*[ModuleCat.{u + 1} Λ]).map f)).naturality c.hom
    dsimp at h h' ⊢
    simp only [Category.assoc]
    rw [reassoc_of% h, h']

/-- The square `Lg^* Res Ψ K ≅ Res Lg^* Ψ K ≅ Res Ψ Lg^* K` of the composites `Res ∘ Ψ`. -/
@[simps]
noncomputable def restrictExtendPullbackSquare :
    (derivedExtendScalars hρ ha Y ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ) ⋙
        L((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙
        (derivedExtendScalars hρ ha Z ⋙ Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ) where
  app K := (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app _ ≫
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).map
      ((derivedExtendScalarsPullbackIso hρ ha g).inv.app K)
  naturality K K' f := by
    have h₁ := (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.naturality
      ((derivedExtendScalars hρ ha Y).map f)
    have h₂ := (derivedExtendScalarsPullbackIso hρ ha g).inv.naturality f
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc]
    rw [reassoc_of% h₁, ← Functor.map_comp, ← Functor.map_comp, h₂]

variable [Finite Λ]

/-- **The reduction of coefficients commutes with proper direct images**, as soon as `Res ∘ Ψ`
is identified with tensor products `- ⊗ᴸ R_Y`, `- ⊗ᴸ R_Z` compatibly with `Lg^*` (`hθ`) and `Res`
commutes with `Rg_*`: through `θ`, the restriction of scalars of `β_g` is the projection map
`Rg_* M ⊗ᴸ R_Y ⟶ Rg_*(M ⊗ᴸ Lg^* R_Y)`, an isomorphism for `g` proper at finite coefficients. -/
theorem isIso_derivedExtendScalarsLowerStarComparison [IsProper g] (R_Y : 𝐃(Y, Λ))
    (R_Z : 𝐃(Z, Λ)) (c : (L((g)^*[ModuleCat.{u + 1} Λ])).obj R_Y ≅ R_Z)
    (θY : (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj R_Y ≅
      derivedExtendScalars hρ ha Y ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ)
    (θZ : (derivedTensor (ModuleCat.{u + 1} Λ) Z).flip.obj R_Z ≅
      derivedExtendScalars hρ ha Z ⋙ Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ)
    (hθ : ∀ K, L((g)^*[ModuleCat.{u + 1} Λ]).map (θY.hom.app K) ≫
        (restrictExtendPullbackSquare hρ ha g).app K =
      (tensorPullbackSquare g R_Y R_Z c).app K ≫ θZ.hom.app _)
    [IsIso (derivedRestrictScalarsLowerStarComparison g (ρ := ρ))] :
    IsIso (derivedExtendScalarsLowerStarComparison hρ ha g) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ g
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  suffices IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
      ((derivedExtendScalarsLowerStarComparison hρ ha g).app M)) from
    isIso_of_reflects_iso _ (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ)
  have h := Adjunction.app_comp_homEquiv_comp_map_counit
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (tensorPullbackSquare g R_Y R_Z c) (restrictExtendPullbackSquare hρ ha g) θY.hom θZ.hom hθ M
  have hD := homEquiv_comp_map_counit_eq hρ ha g M
  have hP : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _
      ((tensorPullbackSquare g R_Y R_Z c).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) Z).flip.obj R_Z).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app M)) =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app M).app R_Y ≫
        R((g)_*[ModuleCat.{u + 1} Λ]).map
          (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj M).map c.hom) := by
    apply
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, rightDerivedLowerStarProjectionMap_app_app,
      Adjunction.homEquiv_naturality_right_symm]
    erw [Equiv.symm_apply_apply]
    simp only [tensorPullbackSquare_app, Functor.flip_obj_map, Category.assoc]
    congr 1
    exact (((derivedTensor (ModuleCat.{u + 1} Λ) Z).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app M)).naturality
        c.hom)
  have hX : (restrictExtendPullbackSquare hρ ha g).app _ ≫
      (derivedExtendScalars hρ ha Z ⋙ Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app M) =
      (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app _ ≫
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).map
          ((derivedExtendScalarsPullbackIso hρ ha g).inv.app _ ≫
            (derivedExtendScalars hρ ha Z).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app M)) := by
    simp only [restrictExtendPullbackSquare_app, Functor.comp_map, Functor.map_comp,
      Category.assoc]
  rw [hX] at h
  erw [hD, hP] at h
  have hI : IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
      ((derivedExtendScalarsLowerStarComparison hρ ha g).app M) ≫
        (derivedRestrictScalarsLowerStarComparison g (ρ := ρ)).app _) := by
    rw [(IsIso.eq_inv_comp _).2 h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((derivedRestrictScalarsLowerStarComparison g (ρ := ρ)).app _)


end Comparison

end AlgebraicGeometry.Etale
