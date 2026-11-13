/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineImageRep
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Local surjectivity of the higher-image colimit comparison

## References

* Stacks Project, Tags 09Z1, 03Q8, 0EZM and 03FD.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The canonical comparison from the stage sheaf colimit is an epimorphism.
This asserts local lifting of sections; it does not assert a representative over
an entire affine object or any uniqueness of representatives (Stacks, Tag 09Z1). -/
theorem epi_higher_image_colimit_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : I, K.obj (op i) ≅
      higherDirectImage Λ ((D.obj i).hom ≫ k) q
        ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (B : Cocone K)
    (eB : B.pt ≅ higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hB : ∀ i : I, B.ι.app (op i) = (eK i).hom ≫
      higherDirectImageOverMap Λ k G q (c.π.app i) ≫ eB.inv) :
    Epi (colimit.desc K B) := by
  classical
  let H := higherDirectImage Λ (c.pt.hom ≫ k) q
    (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  let A := sheafCompose S.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let τ := higherDirectImageRawOverComparison Λ k G q c.pt
  have hτ : Presheaf.IsLocallySurjective S.smallEtaleTopology τ :=
    (isLocallyBijective_higherDirectImagePresheafToSheaf Λ _ _ _).2
  refine ⟨?_⟩
  intro Z a b hab
  have hlegs (i : I) : B.ι.app (op i) ≫ a = B.ι.app (op i) ≫ b := by
    simpa only [colimit.ι_desc_assoc] using
      congrArg (fun f ↦ colimit.ι K (op i) ≫ f) hab
  let a' : H ⟶ Z := eB.inv ≫ a
  let b' : H ⟶ Z := eB.inv ≫ b
  have hraw : τ ≫ (A.map a').hom = τ ≫ (A.map b').hom := by
    apply (Functor.IsCoverDense.restrictHomEquivHom
      (G := Scheme.AffineEtale.Spec S)).symm.injective
    ext U z
    have : IsAffine ((Scheme.AffineEtale.Spec S).obj U.unop).left := by
      rw [Scheme.AffineEtale.Spec_obj_left]
      infer_instance
    obtain ⟨i, t, ht⟩ := exists_higher_image_raw_affine_image_rep Λ k G q D c hc
      ((Scheme.AffineEtale.Spec S).obj U.unop) z
    have hi : higherDirectImageOverMap Λ k G q (c.π.app i) ≫ a' =
        higherDirectImageOverMap Λ k G q (c.π.app i) ≫ b' := by
      have h := congrArg (fun f ↦ (eK i).inv ≫ f) (hlegs i)
      simpa only [hB, Category.assoc, Iso.inv_hom_id_assoc] using h
    have he := congrArg (fun f ↦ (f.hom.app
      (op ((Scheme.AffineEtale.Spec S).obj U.unop)))
        ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app
          (op ((Scheme.AffineEtale.Spec S).obj U.unop)) t)) hi
    change (a'.hom.app _) (τ.app _ z) = (b'.hom.app _) (τ.app _ z)
    change (a'.hom.app _) (((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app _)
      ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app _ t)) =
      (b'.hom.app _) (((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app _)
        ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app _ t)) at he
    simpa only [Functor.op_obj, τ, ht] using he
  have heq : a' = b' := by
    apply (sheafCompose S.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).map_injective
    ext U x
    let Zt := (sheafCompose S.smallEtaleTopology
      (forget (ModuleCat.{u + 1} Λ))).obj Z
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 Zt.property).isSeparated _
      (Presheaf.imageSieve_mem S.smallEtaleTopology τ x)).ext
    rintro V f ⟨t, ht⟩
    have h₁ := ConcreteCategory.congr_hom (a'.hom.naturality f.op) x
    have h₂ := ConcreteCategory.congr_hom (b'.hom.naturality f.op) x
    dsimp at h₁ h₂ ⊢
    change (Z.obj.map f.op) ((a'.hom.app U) x) =
      (Z.obj.map f.op) ((b'.hom.app U) x)
    change τ.app (op V) t = H.obj.map f.op x at ht
    rw [← h₁, ← h₂, ← ht]
    exact ConcreteCategory.congr_hom (congr_app hraw (op V)) t
  have h := congrArg (fun f ↦ eB.hom ≫ f) heq
  simpa only [a', b', Iso.hom_inv_id_assoc] using h

end AlgebraicGeometry.Etale
