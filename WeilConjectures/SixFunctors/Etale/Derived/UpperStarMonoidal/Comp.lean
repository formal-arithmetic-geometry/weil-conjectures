/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalComp
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquareComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp

/-!
# The composition isomorphism of derived pullbacks is monoidal

For morphisms `g₁ : T ⟶ S` and `g₂ : S ⟶ R`, the composition isomorphism
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` is
compatible with the tensor comparisons `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_comp_tensorComparison`).

It is checked on complexes `Qh K`, `Qh M` with `(g₁ ≫ g₂)^* M` K-flat, where the tensor
comparisons are computed from the comonoidal structures of the underived pullbacks, through the
monoidality of the underived composition isomorphism
(`AlgebraicGeometry.Etale.upperStarComp_hom_app_tensor_comp_δ`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme DerivedCategory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)

/-- The compatibility of the composition isomorphism of derived pullbacks with the tensor
comparisons, on complexes `Qh K` and `Qh M`, after the counit
`L(g₁ ≫ g₂)^*(Qh K) ⊗ᴸ L(g₁ ≫ g₂)^*(Qh M) ⟶ Qh((g₁ ≫ g₂)^*K ⊗ (g₁ ≫ g₂)^*M)`. -/
lemma leftDerivedUpperStarComp_tensorComparison_Qh
    (K M : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app
          (((-⊗ᴸ-(R)[A]).obj (Qh.obj K)).obj (Qh.obj M)) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app (Qh.obj K)).app
          (Qh.obj M)) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _) ≫
      ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app (Qh.obj K) ⊗ₘ
        (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app (Qh.obj M)) ≫
      ((g₁₂)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ
        (g₁₂)^*[A].leftDerivedFunctorCounit.app M) ≫
      μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
        (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj M) =
    ((leftDerivedUpperStarTensorComparison A g₁₂).app (Qh.obj K)).app (Qh.obj M) ≫
      ((g₁₂)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ
        (g₁₂)^*[A].leftDerivedFunctorCounit.app M) ≫
      μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
        (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj M) := by
  obtain ⟨shom, hshom⟩ : ∃ shom : ∀ X : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ),
      (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X ⟶ ((g₁)^*[A].mapHomotopyCategory (.up ℤ)).obj
        (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X)), ∀ X, shom X =
        (NatTrans.mapHomotopyCategory (upperStarComp A g₁ g₂ g₁₂ hg).hom (.up ℤ)).app X :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨sinv, hsinv⟩ : ∃ sinv : ∀ X : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ),
      (((g₁)^*[A].mapHomotopyCategory (.up ℤ)).obj
        (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) ⟶
          ((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X), ∀ X, sinv X =
        (NatTrans.mapHomotopyCategory (upperStarComp A g₁ g₂ g₁₂ hg).inv (.up ℤ)).app X :=
    ⟨_, fun _ ↦ rfl⟩
  have hsi (X) : shom X ≫ sinv X = 𝟙 _ := by
    rw [hshom, hsinv, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
      Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  have H (X : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (Qh.obj X) ≫
        L((g₁)^*[A]).map ((g₂)^*[A].leftDerivedFunctorCounit.app X) ≫
          (g₁)^*[A].leftDerivedFunctorCounit.app
            (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) =
        (g₁₂)^*[A].leftDerivedFunctorCounit.app X ≫ Qh.map (shom X) := by
    have h₁ := Functor.leftDerivedFunctorNatIso_hom_app_comp_leftDerivedFunctorCounit_app
      (g₁₂)^*[A] (upperStarComp A g₁ g₂ g₁₂ hg) X
    have h₂ := Functor.leftDerivedFunctorCompIso_hom_app_comp_leftDerivedFunctorCounit_app
      (g₂)^*[A] (g₁)^*[A] X
    rw [hshom, ← h₁, ← h₂]
    simp only [leftDerivedUpperStarComp, Iso.trans_hom, NatTrans.comp_app, assoc]
  have hs (X Y : HomotopyCategory (Sheaf R.smallEtaleTopology A) (.up ℤ)) :
      shom (X ⊗ Y) ≫ ((g₁)^*[A].mapHomotopyCategory (.up ℤ)).map
        (δ ((g₂)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)) X Y) ≫
          δ ((g₁)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)) _ _ =
      δ ((g₁₂)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)) X Y ≫ (shom X ⊗ₘ shom Y) := by
    rw [hshom, hshom, hshom]
    exact Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_comp (.up ℤ)
      (upperStarComp A g₁ g₂ g₁₂ hg).hom (upperStarComp_hom_app_tensor_comp_δ A g₁ g₂ g₁₂ hg)
      X Y
  exact Functor.OplaxMonoidal.comp_app_app_comp_of_lax_square
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg) shom sinv
    (leftDerivedUpperStarTensorComparison_app_app_comp A g₂)
    (leftDerivedUpperStarTensorComparison_app_app_comp A g₁)
    (leftDerivedUpperStarTensorComparison_app_app_comp A g₁₂) hsi H hs K M


/-- **The composition isomorphism of derived pullbacks is monoidal.** For `g₁ : T ⟶ S`,
`g₂ : S ⟶ R` and `g₁₂ = g₁ ≫ g₂`, the square
```
L(g₁₂)^*(K ⊗ᴸ M) ──≅──▶ Lg₁^*Lg₂^*(K ⊗ᴸ M) ──Lg₁^*δ──▶ Lg₁^*(Lg₂^*K ⊗ᴸ Lg₂^*M)
       │ δ                                                       │ δ
       ▼                                                         ▼
L(g₁₂)^*K ⊗ᴸ L(g₁₂)^*M ─────────≅ ⊗ ≅─────────▶ Lg₁^*Lg₂^*K ⊗ᴸ Lg₁^*Lg₂^*M
```
commutes, where `δ` is the tensor comparison
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`. -/
lemma leftDerivedUpperStarComp_hom_app_comp_tensorComparison
    (K M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (((-⊗ᴸ-(R)[A]).obj K).obj M) ≫
        L((g₁)^*[A]).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app M) ≫
          ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ =
      ((leftDerivedUpperStarTensorComparison A g₁₂).app K).app M ≫
        ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K ⊗ₘ
          (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app M) := by
  have := Localization.essSurj (Qh (C := Sheaf R.smallEtaleTopology A))
    (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨P, hP, ⟨iM⟩⟩ := exists_kFlatUpperStar_iso A g₁₂ M
  refine Functor.OplaxMonoidal.comp_app_app_of_iso (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg)
    (Qh.objObjPreimageIso K) iM ?_
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj (Qh.objPreimage K)) _ hP
  have : IsIso (((g₁₂)^*[A].leftDerivedFunctorCounit.app (Qh.objPreimage K) ⊗ₘ
      (g₁₂)^*[A].leftDerivedFunctorCounit.app P) ≫
        μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj (Qh.objPreimage K))
          (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) :=
    IsIso.comp_isIso' inferInstance this
  have := IsIso.mono_of_iso (((g₁₂)^*[A].leftDerivedFunctorCounit.app (Qh.objPreimage K) ⊗ₘ
      (g₁₂)^*[A].leftDerivedFunctorCounit.app P) ≫
        μ Qh (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj (Qh.objPreimage K))
          (((g₁₂)^*[A].mapHomotopyCategory (.up ℤ)).obj P))
  exact Functor.OplaxMonoidal.comp_app_app_of_mono _ _
    (leftDerivedUpperStarComp_tensorComparison_Qh A g₁ g₂ g₁₂ hg _ _)

end AlgebraicGeometry.Etale
