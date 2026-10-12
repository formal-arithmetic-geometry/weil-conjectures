/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.UnitLaw

/-!
# The identity isomorphism of the derived pullback

For a scheme `X`, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarId`) of the derived pullback of pro-étale
sheaves satisfies the left unit law with respect to the composition isomorphisms
`L(𝟙 X ≫ t)^* ≅ Lt^* ⋙ L(𝟙 X)^*`, and it is monoidal: it is compatible with the tensor
comparison `L(𝟙 X)^*(K ⊗ᴸ M) ⟶ L(𝟙 X)^*K ⊗ᴸ L(𝟙 X)^*M`.

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarId_hom_app_Qh_obj`: on the image of a complex,
  the identity isomorphism is the underived one, read through the counit.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_hom_app_comp_leftDerivedUpperStarId_hom_app`:
  the left unit law.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_id_comp`: monoidality.

## Implementation notes

The left unit law is checked on images of complexes through the counits of the derived
pullbacks, where it is the left unit law
`AlgebraicGeometry.ProEtale.upperStarComp_hom_app_comp_upperStarId_hom_app` of the underived
pullbacks. Monoidality is then deduced formally from the left unit law for `𝟙 X ≫ 𝟙 X` and the
monoidality of the composition isomorphisms
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_comp`), using that `L(𝟙 X)^*`
is faithful, being isomorphic to the identity.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

open DerivedCategory

variable {X Y : Scheme.{u}}

/-- On the image `Qh K` of a complex, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is the counit of
`L(𝟙 X)^*` followed by the identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the underived pullback. -/
lemma leftDerivedUpperStarId_hom_app_Qh_obj
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ)) :
    (leftDerivedUpperStarId A X).hom.app (Qh.obj K) =
      (𝟙 X)^*[A].leftDerivedFunctorCounit.app K ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarId A X).hom (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app K) := by
  have h₁ := Functor.leftDerivedFunctorNatIso_hom_app_comp_counit _ (upperStarId A X) K
  have h₂ := (𝟭 (Sheaf (Scheme.ProEt.topology X) A)).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    K
  have h₃ := NatTrans.congr_app
    (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh
      (Sheaf (Scheme.ProEt.topology X) A))) K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h₃
  erw [Category.comp_id, Category.comp_id] at h₃
  rw [Functor.map_comp, ← reassoc_of% h₁, ← h₂, Category.assoc, ← h₃]
  rfl

/-- The transport isomorphism `La^* ≅ Lb^*` along `a = b`, on the image of a complex, read
through the counits. -/
@[reassoc]
lemma leftDerivedUpperStarCongr_hom_app_Qh_obj_comp_counit {a b : X ⟶ Y} (h : a = b)
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)) :
    (leftDerivedUpperStarCongr A h).hom.app (Qh.obj K) ≫
        (b)^*[A].leftDerivedFunctorCounit.app K =
      (a)^*[A].leftDerivedFunctorCounit.app K ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarCongr A h).hom (.up ℤ)).app K) := by
  subst h
  simp [upperStarCongr]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The left unit law of the underived pullbacks, on homotopy categories. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_left (t : X ⟶ Y)
    (K : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (t)^*[A] (𝟙 X)^*[A] (𝟙 X ≫ t)^*[A]
        (upperStarComp A (𝟙 X) t) K ≫
      (NatTrans.mapHomotopyCategory (upperStarId A X).hom (.up ℤ)).app
          (((t)^*[A].mapHomotopyCategory (.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app _ =
      (NatTrans.mapHomotopyCategory (upperStarCongr A (Category.id_comp t)).hom (.up ℤ)).app K := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
  erw [Category.comp_id]
  have h₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl ((t)^*[A] ⋙ (𝟙 X)^*[A]))
      (.up ℤ)).inv.app ((HomotopyCategory.quotient _ _).obj C) = 𝟙 _ := by
    rw [← cancel_mono ((Functor.mapHomotopyCategoryCompIso (Iso.refl ((t)^*[A] ⋙ (𝟙 X)^*[A]))
      (.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj C)), Iso.inv_hom_id_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  simp only [Functor.mapHomotopyCategoryCompHom, h₁, Category.comp_id,
    NatTrans.mapHomotopyCategory_app]
  rw [← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  exact upperStarComp_hom_app_comp_upperStarId_hom_app A t _

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- Natural transformations out of a functor on `D(X_proét)` agree as soon as they agree on the
images `Qh K` of complexes. -/
lemma natTrans_ext_Qh {D : Type*} [Category D]
    {F G : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ D} {α β : F ⟶ G}
    (h : ∀ K, α.app (Qh.obj K) = β.app (Qh.obj K)) : α = β := by
  have := Localization.essSurj (Qh (C := Sheaf (Scheme.ProEt.topology X) A))
    (HomotopyCategory.quasiIso _ (.up ℤ))
  ext Z
  rw [← cancel_epi (F.map (Qh.objObjPreimageIso Z).hom), α.naturality, β.naturality, h]

/-- **Left unit law for the derived pullbacks**: the composition isomorphism
`L(𝟙 X ≫ t)^* ≅ Lt^* ⋙ L(𝟙 X)^*` followed by `L(𝟙 X)^* ≅ 𝟭` is the transport isomorphism along
`𝟙 X ≫ t = t`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_comp_leftDerivedUpperStarId_hom_app (t : X ⟶ Y)
    (Z : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarComp A (𝟙 X) t).hom.app Z ≫
        (leftDerivedUpperStarId A X).hom.app (L((t)^*[A]).obj Z) =
      (leftDerivedUpperStarCongr A (Category.id_comp t)).hom.app Z := by
  let α : L((𝟙 X ≫ t)^*[A]) ⟶ L((t)^*[A]) :=
    (leftDerivedUpperStarComp A (𝟙 X) t).hom ≫
      Functor.whiskerLeft L((t)^*[A]) (leftDerivedUpperStarId A X).hom ≫
        (Functor.rightUnitor _).hom
  suffices hα : α = (leftDerivedUpperStarCongr A (Category.id_comp t)).hom by
    have := NatTrans.congr_app hα Z
    simpa [α] using this
  refine natTrans_ext_Qh A (fun K ↦ ?_)
  have : IsIso ((t)^*[A].leftDerivedFunctorCounit.app K) := by
    rw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
    infer_instance
  rw [← cancel_mono ((t)^*[A].leftDerivedFunctorCounit.app K),
    leftDerivedUpperStarCongr_hom_app_Qh_obj_comp_counit]
  have hn := (leftDerivedUpperStarId A X).hom.naturality ((t)^*[A].leftDerivedFunctorCounit.app K)
  simp only [Functor.id_map] at hn
  simp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.assoc]
  erw [Category.id_comp ((t)^*[A].leftDerivedFunctorCounit.app K)]
  erw [← hn]
  erw [leftDerivedUpperStarId_hom_app_Qh_obj]
  rw [
    leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc, ← Functor.map_comp,
    ← mapHomotopyCategoryCompHom_upperStarComp_id_left]

variable [ProEtale.UpperStarPreservesFlat A]

/-- The transport isomorphism `La^* ≅ Lb^*` along an equality `a = b` commutes with the tensor
comparisons of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarCongr_hom_tensor' {a b : X ⟶ Y} (h : a = b)
    (x y : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((leftDerivedUpperStarTensorComparison A a).app x).app y ≫
        ((leftDerivedUpperStarCongr A h).hom.app x ⊗ₘ (leftDerivedUpperStarCongr A h).hom.app y) =
      (leftDerivedUpperStarCongr A h).hom.app (x ⊗ y) ≫
        ((leftDerivedUpperStarTensorComparison A b).app x).app y := by
  subst h
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, id_tensorHom_id]
  erw [Category.comp_id, Category.id_comp]

/-- Monoidality of `L(𝟙 X)^* ≅ 𝟭` at objects in the image of `L(𝟙 X)^*`. -/
private lemma leftDerivedUpperStarTensorComparison_id_comp_aux
    (a b : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (leftDerivedUpperStarId A X).inv.app (L((𝟙 X)^*[A]).obj a) ⊗ₘ
        (leftDerivedUpperStarId A X).inv.app (L((𝟙 X)^*[A]).obj b) =
      (leftDerivedUpperStarId A X).inv.app
          (L((𝟙 X)^*[A]).obj a ⊗ L((𝟙 X)^*[A]).obj b) ≫
        ((leftDerivedUpperStarTensorComparison A (𝟙 X)).app _).app _ := by
  have hκ (Z : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
      (leftDerivedUpperStarComp A (𝟙 X) (𝟙 X)).hom.app Z =
        (leftDerivedUpperStarCongr A (Category.id_comp (𝟙 X))).hom.app Z ≫
          (leftDerivedUpperStarId A X).inv.app (L((𝟙 X)^*[A]).obj Z) := by
    rw [← leftDerivedUpperStarComp_hom_app_comp_leftDerivedUpperStarId_hom_app, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₁ := leftDerivedUpperStarTensorComparison_comp A (𝟙 X) (𝟙 X) a b
  have h₃ := leftDerivedUpperStarCongr_hom_tensor' A (Category.id_comp (𝟙 X)) a b
  rw [hκ, hκ, hκ, ← tensorHom_comp_tensorHom, reassoc_of% h₃, Category.assoc,
    cancel_epi] at h₁
  have hn := (leftDerivedUpperStarId A X).inv.naturality
    (((leftDerivedUpperStarTensorComparison A (𝟙 X)).app a).app b)
  simp only [Functor.id_map] at hn
  erw [← reassoc_of% hn] at h₁
  rw [cancel_epi] at h₁
  exact h₁

/-- **The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is monoidal**: it commutes with the tensor
comparison of `L(𝟙 X)^*`,
```
  L(𝟙 X)^*(a ⊗ᴸ b) ──comparison──▶ L(𝟙 X)^*a ⊗ᴸ L(𝟙 X)^*b
            \                               │
             \                              │ λ_a ⊗ λ_b
              ────────λ_{a ⊗ b}──────▶  a ⊗ᴸ b
``` -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_id_comp
    (a b : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((leftDerivedUpperStarTensorComparison A (𝟙 X)).app a).app b ≫
        ((leftDerivedUpperStarId A X).hom.app a ⊗ₘ (leftDerivedUpperStarId A X).hom.app b) =
      (leftDerivedUpperStarId A X).hom.app (a ⊗ b) := by
  -- first at `L(𝟙 X)^*a`, `L(𝟙 X)^*b`
  have key : ((leftDerivedUpperStarTensorComparison A (𝟙 X)).app (L((𝟙 X)^*[A]).obj a)).app
        (L((𝟙 X)^*[A]).obj b) ≫
        ((leftDerivedUpperStarId A X).hom.app _ ⊗ₘ (leftDerivedUpperStarId A X).hom.app _) =
      (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj a ⊗ L((𝟙 X)^*[A]).obj b) := by
    rw [← cancel_epi ((leftDerivedUpperStarId A X).inv.app
      (L((𝟙 X)^*[A]).obj a ⊗ L((𝟙 X)^*[A]).obj b)), Iso.inv_hom_id_app,
      ← reassoc_of% (leftDerivedUpperStarTensorComparison_id_comp_aux A a b),
      tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    exact id_tensorHom_id _ _
  -- then transport along `λ⁻¹ : a ≅ L(𝟙 X)^*a`
  have hn := leftDerivedUpperStarTensorComparison_naturality A (𝟙 X)
    ((leftDerivedUpperStarId A X).inv.app a) ((leftDerivedUpperStarId A X).inv.app b)
  have hlam := (leftDerivedUpperStarId A X).hom.naturality
    ((leftDerivedUpperStarId A X).inv.app a ⊗ₘ (leftDerivedUpperStarId A X).inv.app b)
  simp only [Functor.id_map, Functor.id_obj] at hlam
  have e (z : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
      L((𝟙 X)^*[A]).map ((leftDerivedUpperStarId A X).inv.app z) ≫
        (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj z) = 𝟙 _ := by
    rw [(leftDerivedUpperStarId A X).hom.naturality]
    simp
  rw [← cancel_mono ((leftDerivedUpperStarId A X).inv.app a ⊗ₘ
    (leftDerivedUpperStarId A X).inv.app b), Category.assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  erw [id_tensorHom_id, Category.comp_id]
  rw [← hlam, ← key, ← reassoc_of% hn, tensorHom_comp_tensorHom]
  erw [e, e, id_tensorHom_id, Category.comp_id]

end ProEtale

end AlgebraicGeometry
