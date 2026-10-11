/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalNatTrans

/-!
# The composition isomorphisms of the derived pullback are monoidal

For `f : X ⟶ Y` and `g : Y ⟶ Z`, the composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) of the derived pullbacks of étale sheaves of
`Λ`-modules is compatible with the tensor comparisons
`Lh^*(K ⊗ᴸ M) ≅ Lh^*K ⊗ᴸ Lh^*M` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`):

```
L(fg)^*(K ⊗ᴸ M) ─────────────δ_{fg}─────────────▶ L(fg)^*K ⊗ᴸ L(fg)^*M
       │                                                   │
       ▼                                                   ▼
Lf^*Lg^*(K ⊗ᴸ M) ──Lf^*δ_g──▶ Lf^*(Lg^*K ⊗ᴸ Lg^*M) ──δ_f──▶ Lf^*Lg^*K ⊗ᴸ Lf^*Lg^*M
```

The proof goes through the three levels of the construction: the composition isomorphism
`(fg)^* ≅ g^* ⋙ f^*` of the underived pullbacks is monoidal, being conjugate to the monoidal
composition isomorphism of the pushforwards; hence so is its levelwise extension to the homotopy
categories of complexes; and the derived statement follows from the uniqueness of natural
transformations into the left derived bifunctor `(K, M) ↦ L(fg)^*K ⊗ᴸ L(fg)^*M`.

## Main statements

- `AlgebraicGeometry.Etale.isMonoidal_upperStarComp_hom`: the underived statement.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`: the derived statement.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of the pullbacks of étale sheaves of
`Λ`-modules is monoidal: it is conjugate to the composition isomorphism of the pushforwards, which
is monoidal (`AlgebraicGeometry.Etale.isMonoidal_lowerStarComp_hom`). -/
instance isMonoidal_upperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
  have h : (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom =
      (conjugateEquiv ((Etale.upperStarLowerStarAdjunction _ h₂).comp
        (Etale.upperStarLowerStarAdjunction _ h₁))
        (Etale.upperStarLowerStarAdjunction _ h₁₂)).symm
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
    rw [Equiv.eq_symm_apply]
    exact congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp _ h₁ h₂ h₁₂ hh)
  rw [h]
  exact isMonoidal_conjugateEquiv_symm _ _ _

section Derived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

open DerivedCategory

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
  [(f)^*[A].PreservesFlat] [(g)^*[A].PreservesFlat] [(fg)^*[A].PreservesFlat]

/-- The components of the derived tensor comparison counit
`AlgebraicGeometry.Etale.derivedTensorLeftDerivedUpperStarCounit`. -/
lemma derivedTensorLeftDerivedUpperStarCounit_app_app {W V : Scheme.{u}} (h : W ⟶ V)
    (K M : HomotopyCategory (Sheaf V.smallEtaleTopology A) (.up ℤ)) :
    ((derivedTensorLeftDerivedUpperStarCounit A h).app K).app M =
      ((h)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (h)^*[A].leftDerivedFunctorCounit.app M) ≫
        Functor.LaxMonoidal.μ Qh (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
          (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj M) := by
  rw [tensorHom_def]
  dsimp [derivedTensorLeftDerivedUpperStarCounit, derivedTensor]
  rw [Category.assoc]
  rfl

/-- The tensor comparison `L(fg)^*(K ⊗ᴸ M) ⟶ L(fg)^*K ⊗ᴸ L(fg)^*M` obtained through the
composition isomorphism `L(fg)^* ≅ Lg^* ⋙ Lf^*` and the tensor comparisons of `Lg^*` and `Lf^*`.
By `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_eq_comp` it is the tensor
comparison of `L(fg)^*`. -/
noncomputable def leftDerivedUpperStarTensorComparisonComp :
    leftDerivedUpperStarDerivedTensor A fg ⟶ derivedTensorLeftDerivedUpperStar A fg where
  app K :=
    { app M := (leftDerivedUpperStarComp A f g fg hfg).hom.app _ ≫
          (L((f)^*[A])).map (((leftDerivedUpperStarTensorComparison A g).app K).app M) ≫
          ((leftDerivedUpperStarTensorComparison A f).app _).app _ ≫
          ((leftDerivedUpperStarComp A f g fg hfg).inv.app K ⊗ₘ
            (leftDerivedUpperStarComp A f g fg hfg).inv.app M)
      naturality M M' φ := by
        have h₁ := (leftDerivedUpperStarComp A f g fg hfg).hom.naturality
          ((((derivedTensor A Z).obj K).map φ))
        have h₂ := ((leftDerivedUpperStarTensorComparison A g).app K).naturality φ
        have h₃ := ((leftDerivedUpperStarTensorComparison A f).app ((L((g)^*[A])).obj K)).naturality
          ((L((g)^*[A])).map φ)
        dsimp at h₁ h₂ h₃ ⊢
        simp only [Category.assoc]
        rw [reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc, reassoc_of% h₃]
        have h₄ := (leftDerivedUpperStarComp A f g fg hfg).inv.naturality φ
        dsimp at h₄
        dsimp only [derivedTensor, curriedTensor_obj_map]
        rw [whiskerLeft_comp_tensorHom, tensorHom_comp_whiskerLeft, h₄] }
  naturality K K' ψ := by
    ext M
    have h₁ := (leftDerivedUpperStarComp A f g fg hfg).hom.naturality
      ((((derivedTensor A Z).map ψ).app M))
    have h₂ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A g).naturality ψ) M
    have h₃ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A f).naturality
      ((L((g)^*[A])).map ψ)) ((L((g)^*[A])).obj M)
    have h₄ := (leftDerivedUpperStarComp A f g fg hfg).inv.naturality ψ
    dsimp at h₁ h₂ h₃ h₄ ⊢
    simp only [Category.assoc]
    rw [reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc, reassoc_of% h₃]
    dsimp only [derivedTensor, curriedTensor_map_app]
    rw [whiskerRight_comp_tensorHom, tensorHom_comp_whiskerRight, h₄]

/-- The tensor comparison of a derived pullback is natural in both variables at once. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_naturality {W V : Scheme.{u}} (h : W ⟶ V)
    [(h)^*[A].PreservesFlat] {K K' M M' : DerivedCategory (Sheaf V.smallEtaleTopology A)}
    (a : K ⟶ K') (b : M ⟶ M') :
    (L((h)^*[A])).map (a ⊗ₘ b) ≫ ((leftDerivedUpperStarTensorComparison A h).app K').app M' =
      ((leftDerivedUpperStarTensorComparison A h).app K).app M ≫
        ((L((h)^*[A])).map a ⊗ₘ (L((h)^*[A])).map b) := by
  have h₁ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A h).naturality a) M
  have h₂ := ((leftDerivedUpperStarTensorComparison A h).app K').naturality b
  dsimp [derivedTensor] at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc,
    ← tensorHom_def]

variable [NatTrans.IsMonoidal (Etale.upperStarComp A f g fg hfg).hom]

set_option maxHeartbeats 1600000 in
-- the comparison of the two derived bifunctor transformations unfolds the derived tensor product
/-- The tensor comparison of `L(fg)^*` is the one obtained through the composition isomorphism
`L(fg)^* ≅ Lg^* ⋙ Lf^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparisonComp`).
Both are natural transformations into the left derived bifunctor
`(K, M) ↦ L(fg)^*K ⊗ᴸ L(fg)^*M`, so it suffices to compare them on complexes, where it is the
monoidality of the composition isomorphism `(fg)^* ≅ g^* ⋙ f^*` of the underived pullbacks. -/
theorem leftDerivedUpperStarTensorComparison_eq_comp :
    leftDerivedUpperStarTensorComparison A fg =
      leftDerivedUpperStarTensorComparisonComp A f g fg hfg := by
  refine Functor.leftDerived₂_ext (derivedTensorLeftDerivedUpperStar A fg)
    (derivedTensorLeftDerivedUpperStarCounit A fg) (HomotopyCategory.quasiIso _ (.up ℤ))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext K M
  dsimp only [NatTrans.comp_app, Functor.whiskeringLeft₂_obj_obj_map_app_app]
  rw [derivedTensorLeftDerivedUpperStarCounit_app_app,
    leftDerivedUpperStarTensorComparison_app_app_comp]
  let X := Functor.mapHomotopyCategoryCompNatTrans (g)^*[A] (f)^*[A] (fg)^*[A]
    (Etale.upperStarComp A f g fg hfg).hom
  have hX (P : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ)) :
      (fg)^*[A].leftDerivedFunctorCounit.app P ≫ Qh.map (X P) =
        (leftDerivedUpperStarComp A f g fg hfg).hom.app (Qh.obj P) ≫
          (L((f)^*[A])).map ((g)^*[A].leftDerivedFunctorCounit.app P) ≫
            (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P) :=
    (leftDerivedUpperStarComp_hom_app_comp_counit A f g fg hfg P).symm
  have hK : IsIso (X K) := Functor.isIso_mapHomotopyCategoryCompNatTrans _ _ _ _ K
  have hM : IsIso (X M) := Functor.isIso_mapHomotopyCategoryCompNatTrans _ _ _ _ M
  have : IsIso (Qh.map (X K ⊗ₘ X M)) := Functor.map_isIso _ _
  rw [← cancel_mono (Qh.map (X K ⊗ₘ X M))]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [Functor.mapHomotopyCategoryCompNatTrans_tensor, ← Functor.LaxMonoidal.μ_natural,
    tensorHom_comp_tensorHom_assoc, hX, hX]
  dsimp only [leftDerivedUpperStarTensorComparisonComp]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← tensorHom_comp_tensorHom_assoc, ← leftDerivedUpperStarTensorComparison_naturality_assoc]
  simp only [Functor.comp_obj]
  rw [leftDerivedUpperStarTensorComparison_app_app_comp, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc, leftDerivedUpperStarTensorComparison_app_app_comp]
  have e₁ : (L((f)^*[A])).map ((L((g)^*[A])).map (μ Qh K M) ≫
      (g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M) ≫
        Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)) =
      (L((f)^*[A])).map ((L((g)^*[A])).map (μ Qh K M)) ≫
        (L((f)^*[A])).map ((g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M)) ≫
          (L((f)^*[A])).map (Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)) := by
    simp only [Functor.map_comp]
  have hn : (L((f)^*[A])).map (Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)) ≫
      (f)^*[A].leftDerivedFunctorCounit.app
        (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K ⊗
          ((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) =
      (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj (K ⊗ M)) ≫
        Qh.map (((f)^*[A].mapHomotopyCategory (.up ℤ)).map
          (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)) :=
    (f)^*[A].leftDerivedFunctorCounit.naturality (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)
  have hc : (leftDerivedUpperStarComp A f g fg hfg).hom.app
        (((derivedTensor A Z).obj (Qh.obj K)).obj (Qh.obj M)) ≫
        (L((f)^*[A])).map ((L((g)^*[A])).map (μ Qh K M)) =
      (L((fg)^*[A])).map (μ Qh K M) ≫
        (leftDerivedUpperStarComp A f g fg hfg).hom.app (Qh.obj (K ⊗ M)) :=
    ((leftDerivedUpperStarComp A f g fg hfg).hom.naturality (μ Qh K M)).symm
  have e₂ : Qh.map ((g)^*[A].mapHomotopyCategoryCompNatTrans (f)^*[A] (fg)^*[A]
      (Etale.upperStarComp A f g fg hfg).hom (K ⊗ M) ≫
        ((f)^*[A].mapHomotopyCategory (.up ℤ)).map
          (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M) ≫
          δ ((f)^*[A].mapHomotopyCategory (.up ℤ))
            (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
            (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M)) =
      Qh.map (X (K ⊗ M)) ≫ Qh.map (((f)^*[A].mapHomotopyCategory (.up ℤ)).map
          (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M)) ≫
        Qh.map (δ ((f)^*[A].mapHomotopyCategory (.up ℤ))
            (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
            (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M)) := by
    simp only [Functor.map_comp]
    rfl
  rw [e₁, Category.assoc, Category.assoc, reassoc_of% hn, reassoc_of% hc,
    ← reassoc_of% (hX (K ⊗ M)), e₂]

omit [NatTrans.IsMonoidal (Etale.upperStarComp A f g fg hfg).hom] in
/-- The counit `η : Lh^* Λ_Y ⟶ Λ_X` of the oplax monoidal derived pullback, in terms of the counit
of the left derived functor. -/
lemma leftDerivedUpperStar_η_eq {W V : Scheme.{u}} (h : W ⟶ V) [(h)^*[A].PreservesFlat] :
    letI := leftDerivedUpperStarOplaxMonoidal A h
    haveI := DerivedCategory.isIso_ε_Qh (Sheaf W.smallEtaleTopology A)
    Functor.OplaxMonoidal.η (L((h)^*[A])) = (L((h)^*[A])).map (Functor.LaxMonoidal.ε Qh) ≫
      (h)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
        Qh.map (Functor.OplaxMonoidal.η ((h)^*[A].mapHomotopyCategory (.up ℤ))) ≫
          CategoryTheory.inv (Functor.LaxMonoidal.ε Qh) :=
  rfl

set_option maxHeartbeats 800000 in
-- the kernel unfolds the counits of three left derived functors
/-- The composition isomorphism `L(fg)^* ≅ Lg^* ⋙ Lf^*` is compatible with the counits
`η : Lh^* Λ ⟶ Λ` of the oplax monoidal derived pullbacks. -/
theorem leftDerivedUpperStarComp_hom_app_unit :
    letI := leftDerivedUpperStarOplaxMonoidal A f
    letI := leftDerivedUpperStarOplaxMonoidal A g
    letI := leftDerivedUpperStarOplaxMonoidal A fg
    (leftDerivedUpperStarComp A f g fg hfg).hom.app (𝟙_ _) ≫
        (L((f)^*[A])).map (Functor.OplaxMonoidal.η (L((g)^*[A]))) ≫
          Functor.OplaxMonoidal.η (L((f)^*[A])) =
      Functor.OplaxMonoidal.η (L((fg)^*[A])) := by
  rw [leftDerivedUpperStar_η_eq, leftDerivedUpperStar_η_eq, leftDerivedUpperStar_η_eq]
  have := DerivedCategory.isIso_ε_Qh (Sheaf Y.smallEtaleTopology A)
  have e₁ : (L((f)^*[A])).map ((L((g)^*[A])).map (Functor.LaxMonoidal.ε Qh) ≫
        (g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
          Qh.map (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ))) ≫
            CategoryTheory.inv (Functor.LaxMonoidal.ε Qh)) ≫
        (L((f)^*[A])).map (Functor.LaxMonoidal.ε Qh) =
      (L((f)^*[A])).map ((L((g)^*[A])).map (Functor.LaxMonoidal.ε Qh)) ≫
        (L((f)^*[A])).map ((g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _)) ≫
          (L((f)^*[A])).map
            (Qh.map (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ)))) := by
    simp only [← Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn : (L((f)^*[A])).map
        (Qh.map (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ)))) ≫
        (f)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) =
      (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj (𝟙_ _)) ≫
        Qh.map (((f)^*[A].mapHomotopyCategory (.up ℤ)).map
          (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ)))) :=
    (f)^*[A].leftDerivedFunctorCounit.naturality _
  have hc : (leftDerivedUpperStarComp A f g fg hfg).hom.app (𝟙_ _) ≫
        (L((f)^*[A])).map ((L((g)^*[A])).map (Functor.LaxMonoidal.ε Qh)) =
      (L((fg)^*[A])).map (Functor.LaxMonoidal.ε Qh) ≫
        (leftDerivedUpperStarComp A f g fg hfg).hom.app (Qh.obj (𝟙_ _)) :=
    ((leftDerivedUpperStarComp A f g fg hfg).hom.naturality _).symm
  have hX := (leftDerivedUpperStarComp_hom_app_comp_counit A f g fg hfg (𝟙_ _)).symm
  have hu := Functor.mapHomotopyCategoryCompNatTrans_η (g)^*[A] (f)^*[A] (fg)^*[A]
    (Etale.upperStarComp A f g fg hfg).hom
  have e₂ := congrArg Qh.map hu
  simp only [Functor.map_comp] at e₂
  rw [reassoc_of% e₁, reassoc_of% hn, reassoc_of% hc, ← reassoc_of% hX]
  rw [← e₂]
  simp only [Category.assoc]
  rfl

end Derived

end Etale

end AlgebraicGeometry
