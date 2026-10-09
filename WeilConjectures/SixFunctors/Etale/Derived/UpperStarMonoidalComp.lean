/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalComp
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapComp
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp

/-!
# The derived pullback tensor comparison and composition

For morphisms of schemes `h₁ : T ⟶ S` and `h₂ : S ⟶ R` with composite `h₁₂`, the comparison
`Lh₁₂^*(K ⊗ᴸ M) ⟶ Lh₁₂^*K ⊗ᴸ Lh₁₂^*M` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison` is the composite of the
comparisons for `h₂` and `h₁`, up to the composition isomorphism
`Lh₁₂^* ≅ Lh₂^* ⋙ Lh₁^*` of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`:
```
  Lh₁₂^*(K ⊗ᴸ M) ────────────────comparison───────────────▶ Lh₁₂^*K ⊗ᴸ Lh₁₂^*M
       │                                                            │
       ≅                                                            ≅
       ▼                                                            ▼
  Lh₁^*Lh₂^*(K ⊗ᴸ M) ──Lh₁^*(comparison)──▶ Lh₁^*(Lh₂^*K ⊗ᴸ Lh₂^*M) ──comparison──▶ ⋯
```
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`). Both sides are maps into
a left derived bifunctor, so it suffices to compare them on objects of the homotopy category,
where this is the compatibility of the underived composition isomorphism
`AlgebraicGeometry.Etale.upperStarComp` with the oplax monoidal structures
(`AlgebraicGeometry.Etale.upperStarComp_hom_app_tensor_comp_δ`), passed to complexes by
`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_comp`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

section

variable {X : Scheme.{u}}

/-- The morphism `f ⊗ᴸ g` of the derived tensor product bifunctor is the tensor product of
morphisms of the monoidal structure on `D(X_ét)`. -/
lemma derivedTensor_map_app_comp_obj_map
    {K K' M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K') (g : M ⟶ M') :
    ((-⊗ᴸ-(X)[A]).map f).app M ≫ ((-⊗ᴸ-(X)[A]).obj K').map g = f ⊗ₘ g := by
  rw [tensorHom_def]
  rfl

/-- The morphism `f ⊗ᴸ g` of the derived tensor product bifunctor is the tensor product of
morphisms of the monoidal structure on `D(X_ét)`. -/
lemma derivedTensor_obj_map_comp_map_app
    {K K' M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K') (g : M ⟶ M') :
    ((-⊗ᴸ-(X)[A]).obj K).map g ≫ ((-⊗ᴸ-(X)[A]).map f).app M' = f ⊗ₘ g := by
  rw [tensorHom_def']
  rfl

end

section

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The counit of `(K, M) ↦ Lg^*(K ⊗ᴸ M)` at `(K, M)`. -/
lemma leftDerivedUpperStarDerivedTensorCounit_app_app
    (K M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarDerivedTensorCounit A g).app K).app M =
      L((g)^*[A]).map (((μNatTrans Qh).app K).app M) ≫
        (g)^*[A].leftDerivedFunctorCounit.app (((curriedTensor _).obj K).obj M) :=
  rfl

/-- The counit of `(K, M) ↦ Lg^*K ⊗ᴸ Lg^*M` at `(K, M)`. -/
lemma derivedTensorLeftDerivedUpperStarCounit_app_app
    (K M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((derivedTensorLeftDerivedUpperStarCounit A g).app K).app M =
      ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        ((μNatTrans Qh).app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)).app
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) := by
  rw [← derivedTensor_map_app_comp_obj_map, Category.assoc]
  rfl

variable [(g)^*[A].PreservesFlat]

/-- The defining property of the comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, as an identity of
natural transformations of bifunctors on homotopy categories. -/
lemma leftDerivedUpperStarTensorComparison_fac :
    (((Functor.whiskeringLeft₂ _).obj Qh).obj Qh).map (leftDerivedUpperStarTensorComparison A g) ≫
        derivedTensorLeftDerivedUpperStarCounit A g =
      leftDerivedUpperStarDerivedTensorCounit A g ≫
        Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh :=
  Functor.leftDerived₂NatTrans_fac _ _ _ _ _ _ _

/-- The defining property of the comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` at complexes
`K` and `M`:
```
  Lg^*(Qh K ⊗ᴸ Qh M) ──comparison──▶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)
          │                                    │
          │ Lg^*(μ) ≫ counit                   │ (counit ⊗ counit) ≫ μ
          ▼                                    ▼
   Qh(g^*(K ⊗ M)) ─────────Qh(δ)──────▶ Qh(g^*K ⊗ g^*M)
```
-/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_app_app_comp_counit
    (K M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj K)).app (Qh.obj M) ≫
        ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        ((μNatTrans Qh).app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)).app
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) =
      L((g)^*[A]).map (((μNatTrans Qh).app K).app M) ≫
        (g)^*[A].leftDerivedFunctorCounit.app (((curriedTensor _).obj K).obj M) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app K).app
          M) := by
  rw [← derivedTensorLeftDerivedUpperStarCounit_app_app, ← Category.assoc,
    ← leftDerivedUpperStarDerivedTensorCounit_app_app]
  exact congr_app (congr_app (leftDerivedUpperStarTensorComparison_fac A g) K) M

/-- Naturality of the comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` in both variables. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_naturality
    {K K' M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (f : K ⟶ K') (f' : M ⟶ M') :
    ((leftDerivedUpperStarTensorComparison A g).app K).app M ≫
        (L((g)^*[A]).map f ⊗ₘ L((g)^*[A]).map f') =
      L((g)^*[A]).map (f ⊗ₘ f') ≫ ((leftDerivedUpperStarTensorComparison A g).app K').app M' := by
  rw [← derivedTensor_map_app_comp_obj_map, ← derivedTensor_map_app_comp_obj_map,
    Functor.map_comp, Category.assoc]
  erw [← NatTrans.naturality_app_assoc (leftDerivedUpperStarTensorComparison A g) M f,
    ((leftDerivedUpperStarTensorComparison A g).app K').naturality f']
  rfl

end

section

variable {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)

/-- The isomorphism `h₁₂^* K ≅ h₁^*(h₂^* K)` in the homotopy category of étale sheaves on `T`,
for a complex `K` on `R`, induced by the composition isomorphism
`AlgebraicGeometry.Etale.upperStarComp`. -/
noncomputable def mapHomotopyCategoryUpperStarCompIso
    (K : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    ((h₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K ≅
      ((h₁)^*[A].mapHomotopyCategory (.up ℤ)).obj (((h₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
    where
  hom := (NatTrans.mapHomotopyCategory (upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom (.up ℤ)).app K
  inv := (NatTrans.mapHomotopyCategory (upperStarComp A h₁ h₂ h₁₂ hh₁₂).inv (.up ℤ)).app K
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
    rfl

/-- The composition isomorphism `Lh₁₂^* ≅ Lh₂^* ⋙ Lh₁^*` is compatible with the counits of
the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_comp_counit
    (K : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app (Qh.obj K) ≫
        L((h₁)^*[A]).map ((h₂)^*[A].leftDerivedFunctorCounit.app K) ≫
        (h₁)^*[A].leftDerivedFunctorCounit.app (((h₂)^*[A].mapHomotopyCategory _).obj K) =
      (h₁₂)^*[A].leftDerivedFunctorCounit.app K ≫
        Qh.map (mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ K).hom :=
  Functor.leftDerivedFunctorCompIso_hom_app_comp_counit _ _ _ K

/-- The inverse of the composition isomorphism `Lh₁₂^* ≅ Lh₂^* ⋙ Lh₁^*` is compatible with the
counits of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_comp_counit
    (K : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app (Qh.obj K) ≫
        (h₁₂)^*[A].leftDerivedFunctorCounit.app K =
      L((h₁)^*[A]).map ((h₂)^*[A].leftDerivedFunctorCounit.app K) ≫
        (h₁)^*[A].leftDerivedFunctorCounit.app (((h₂)^*[A].mapHomotopyCategory _).obj K) ≫
        Qh.map (mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ K).inv := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app (Qh.obj K)),
    Iso.hom_inv_id_app_assoc, leftDerivedUpperStarComp_hom_app_comp_counit_assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

set_option maxHeartbeats 1600000 in
-- The instance arguments of `mapHomotopyCategoryδNatTrans_comp` for three categories of étale
-- sheaves, and the kernel check of the identification of `K(h₁^*) ∘ K(h₂^*)` with
-- `K(h₂^* ⋙ h₁^*)`, are expensive.
omit [Abelian.HasFunctorialFlatResolution A] in
/-- The underived composition isomorphism `h₁₂^* ≅ h₂^* ⋙ h₁^*` is compatible with the
comparisons `δ` on homotopy categories. -/
lemma mapHomotopyCategory_upperStarComp_δ
    (K M : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    (mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ (((curriedTensor _).obj K).obj M)).hom ≫
      ((h₁)^*[A].mapHomotopyCategory (.up ℤ)).map
        (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (h₂)^*[A]).app K).app M) ≫
      ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (h₁)^*[A]).app
        (((h₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K)).app
        (((h₂)^*[A].mapHomotopyCategory (.up ℤ)).obj M) ≫
      ((mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ K).inv ⊗ₘ
        (mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ M).inv) =
      ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (h₁₂)^*[A]).app K).app M := by
  have := Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_comp (.up ℤ)
    (upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom (upperStarComp_hom_app_tensor_comp_δ A h₁ h₂ h₁₂ hh₁₂)
    K M
  erw [reassoc_of% this]
  rw [tensorHom_comp_tensorHom]
  erw [(mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ K).hom_inv_id,
    (mapHomotopyCategoryUpperStarCompIso A h₁ h₂ h₁₂ hh₁₂ M).hom_inv_id, id_tensorHom_id]
  exact Category.comp_id _

variable [Etale.UpperStarPreservesFlat A]

/-- The components of the comparison `Lh₁₂^*(K ⊗ᴸ M) ⟶ Lh₁₂^*K ⊗ᴸ Lh₁₂^*M` obtained from those
of `h₂` and `h₁` through the composition isomorphism `Lh₁₂^* ≅ Lh₂^* ⋙ Lh₁^*`. -/
lemma compComparison_leftDerivedUpperStarTensorComparison_app_app
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((Adjunction.compComparison (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂)
        (leftDerivedUpperStarTensorComparison A h₂)
        (leftDerivedUpperStarTensorComparison A h₁)).app K).app M =
      (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app (((-⊗ᴸ-(R)[A]).obj K).obj M) ≫
        L((h₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A h₂).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A h₁).app (L((h₂)^*[A]).obj K)).app
          (L((h₂)^*[A]).obj M) ≫
        ((leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app K ⊗ₘ
          (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app M) := by
  rw [Adjunction.compComparison_app_app, ← derivedTensor_obj_map_comp_map_app]

set_option maxHeartbeats 1000000 in
-- The rewrites below take place in derived categories of étale sheaves, where unifying the
-- objects is expensive.
/-- **The derived pullback tensor comparison of a composite.** The comparison
`Lh₁₂^*(K ⊗ᴸ M) ⟶ Lh₁₂^*K ⊗ᴸ Lh₁₂^*M` is obtained from those of `h₂` and `h₁` through the
composition isomorphism `Lh₁₂^* ≅ Lh₂^* ⋙ Lh₁^*`. Both sides are maps into a left derived
bifunctor, so it suffices to compare them on objects of the homotopy category, where it is
`AlgebraicGeometry.Etale.mapHomotopyCategory_upperStarComp_δ`. -/
theorem leftDerivedUpperStarTensorComparison_eq_compComparison :
    leftDerivedUpperStarTensorComparison A h₁₂ =
      Adjunction.compComparison (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂)
        (leftDerivedUpperStarTensorComparison A h₂)
        (leftDerivedUpperStarTensorComparison A h₁) := by
  refine Functor.leftDerived₂_ext _ (derivedTensorLeftDerivedUpperStarCounit A h₁₂)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext K M
  simp only [NatTrans.comp_app, Functor.whiskeringLeft₂_obj_obj_map_app_app]
  rw [derivedTensorLeftDerivedUpperStarCounit_app_app,
    leftDerivedUpperStarTensorComparison_app_app_comp_counit,
    compComparison_leftDerivedUpperStarTensorComparison_app_app]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, leftDerivedUpperStarComp_inv_app_comp_counit,
    leftDerivedUpperStarComp_inv_app_comp_counit, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom, μNatTrans_app_app, μNatTrans_app_app]
  simp only [Category.assoc]
  rw [μ_natural, leftDerivedUpperStarTensorComparison_naturality_assoc]
  have h₁fac := leftDerivedUpperStarTensorComparison_app_app_comp_counit A h₁
    (((h₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K) (((h₂)^*[A].mapHomotopyCategory (.up ℤ)).obj M)
  have h₂fac := leftDerivedUpperStarTensorComparison_app_app_comp_counit A h₂ K M
  rw [μNatTrans_app_app, μNatTrans_app_app] at h₁fac h₂fac
  simp only [Functor.comp_obj]
  rw [reassoc_of% h₁fac, ← L((h₁)^*[A]).map_comp_assoc, ← L((h₁)^*[A]).map_comp_assoc,
    Category.assoc, h₂fac]
  have hc := (h₁)^*[A].leftDerivedFunctorCounit.naturality
    (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (h₂)^*[A]).app K).app M)
  have he := (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.naturality (μ Qh K M)
  have hKC := leftDerivedUpperStarComp_hom_app_comp_counit A h₁ h₂ h₁₂ hh₁₂
    (((curriedTensor _).obj K).obj M)
  simp only [Functor.comp_map, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hc he
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% hc]
  erw [← reassoc_of% he, reassoc_of% hKC]
  rw [← Qh.map_comp, ← Qh.map_comp, ← Qh.map_comp, mapHomotopyCategory_upperStarComp_δ]

/-- **The derived pullback tensor comparison of a composite**, objectwise:
```
  Lh₁₂^*(K ⊗ᴸ M) ──────────────comparison──────────────▶ Lh₁₂^*K ⊗ᴸ Lh₁₂^*M
        │                                                         │
        ≅                                                         ≅
        ▼                                                         ▼
  Lh₁^*Lh₂^*(K ⊗ᴸ M) ──▶ Lh₁^*(Lh₂^*K ⊗ᴸ Lh₂^*M) ──▶ Lh₁^*Lh₂^*K ⊗ᴸ Lh₁^*Lh₂^*M
```
-/
lemma leftDerivedUpperStarTensorComparison_comp
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A h₁₂).app K).app M ≫
        ((leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app K ⊗ₘ
          (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app M) =
      (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app (((-⊗ᴸ-(R)[A]).obj K).obj M) ≫
        L((h₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A h₂).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A h₁).app (L((h₂)^*[A]).obj K)).app
          (L((h₂)^*[A]).obj M) := by
  rw [leftDerivedUpperStarTensorComparison_eq_compComparison A h₁ h₂ h₁₂ hh₁₂,
    compComparison_leftDerivedUpperStarTensorComparison_app_app]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

end

end Etale

end AlgebraicGeometry
