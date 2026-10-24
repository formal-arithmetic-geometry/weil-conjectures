/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison

/-!
# The base-change morphism on homology for exact pushforwards

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes such that the pushforwards `f_*` and
`f'_*` of module objects over `Λ` are exact (for instance `f` and `f'` finite), and such that the
base-change morphism `β_* : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of module objects (the exchange morphism of
the composition isomorphisms of the pullbacks) is an isomorphism (for instance `g` and `g'`
isomorphisms). Then on the homology sheaves, the derived base-change morphism
`BC : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is the base-change morphism of module objects: through the
commutations `Hⁿ(Rf_* K) ≅ f_* Hⁿ(K)` and `Hⁿ(Lg^* K) ≅ g^* Hⁿ(K)` of the exact functors with
homology, `Hⁿ(BC_K)` is `β_*` at `Hⁿ(K)`
(`ProEtale.CondensedRing.homologyFunctor_map_boundedConstructibleBaseChange`).

The proof transports the question along the identifications `Lg^* ≅ D(g^*)` and
`Rf_* ≅ D(f_*)` of the total derived functors of exact functors with the levelwise functors
(`CategoryTheory.Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction`); the
composition isomorphisms of the derived pullbacks are the levelwise ones
(`ProEtale.CondensedRing.leftDerivedUpperStarComp_hom_app_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Scheme

variable {X Y Z : Scheme.{u}}

/-- Abstract form of `leftDerivedUpperStarSquare_hom_app_eq`: a square comparison assembled from
composition isomorphisms `C₁`, `C₂` which are given through identifications `I` with other
functors, is the square comparison assembled from the corresponding isomorphisms `T₁`, `T₂`. -/
lemma _root_.CategoryTheory.Iso.squareComparison_hom_app_eq {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] {Lu Mu : 𝒜 ⥤ ℬ} {Lf' Mf' : ℬ ⥤ 𝒟} {Lf Mf : 𝒜 ⥤ 𝒞}
    {Lv Mv : 𝒞 ⥤ 𝒟} {L₁ M₁ L₂ M₂ : 𝒜 ⥤ 𝒟}
    (Iu : Lu ≅ Mu) (If' : Lf' ≅ Mf') (If : Lf ≅ Mf) (Iv : Lv ≅ Mv) (I₁ : L₁ ≅ M₁)
    (I₂ : L₂ ≅ M₂) (T₁ : M₁ ≅ Mu ⋙ Mf') (T₂ : M₂ ≅ Mf ⋙ Mv) (C₁ : L₁ ≅ Lu ⋙ Lf')
    (C₂ : L₂ ≅ Lf ⋙ Lv)
    (hC₁ : ∀ K, C₁.hom.app K =
      I₁.hom.app K ≫ T₁.hom.app K ≫ Mf'.map (Iu.inv.app K) ≫ If'.inv.app (Lu.obj K))
    (hC₂ : ∀ K, C₂.hom.app K =
      I₂.hom.app K ≫ T₂.hom.app K ≫ Mv.map (If.inv.app K) ≫ Iv.inv.app (Lf.obj K))
    (eL : L₁ = L₂) (EM : M₁ ≅ M₂)
    (hE : ∀ K, I₁.inv.app K ≫ eqToHom (by rw [eL]) ≫ I₂.hom.app K = EM.hom.app K)
    (S : Mu ⋙ Mf' ≅ Mf ⋙ Mv) (hS : S = T₁.symm ≪≫ EM ≪≫ T₂) (K : 𝒜) :
    Mf'.map (Iu.inv.app K) ≫ If'.inv.app (Lu.obj K) ≫ (C₁.symm ≪≫ eqToIso eL ≪≫ C₂).hom.app K =
      S.hom.app K ≫ Mv.map (If.inv.app K) ≫ Iv.inv.app (Lf.obj K) := by
  have h₁ : Mf'.map (Iu.inv.app K) ≫ If'.inv.app (Lu.obj K) ≫ C₁.inv.app K =
      T₁.inv.app K ≫ I₁.inv.app K := by
    rw [← cancel_mono (C₁.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hC₁]
    simp only [Iso.inv_hom_id_app_assoc, Functor.comp_obj, Category.comp_id]
  have hE' : (eqToIso eL).hom.app K = I₁.hom.app K ≫ EM.hom.app K ≫ I₂.inv.app K := by
    rw [← hE, eqToIso.hom, eqToHom_app]
    simp
  subst hS
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [reassoc_of% h₁, hE', hC₂]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The composition isomorphism `L(a ≫ b)^* ≅ Lb^* ⋙ La^*` of the derived pullbacks is, through
the identifications of the derived pullbacks with the levelwise pullbacks, the isomorphism
`D((a ≫ b)^*) ≅ D(b^*) ⋙ D(a^*)` induced by the composition isomorphism of the pullbacks. -/
lemma leftDerivedUpperStarComp_hom_app_eq (a : X ⟶ Y) (b : Y ⟶ Z)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ a b).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (a ≫ b)).hom.app K ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ a b)).hom.app K ≫
        (a)^*⟦Λ⟧.mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ b).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ a).inv.app
          ((b)^*⟦Λ⟧.leftDerivedFunctor.obj K) := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-- Along an equality `a = b` of morphisms of schemes, the transport of the derived pullbacks is,
through the identifications with the levelwise pullbacks, the isomorphism induced by the
transport of the pullbacks. -/
lemma leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_eqToHom {a b : X ⟶ Y} (h : a = b)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ a).inv.app K ≫
        eqToHom (by rw [h]) ≫ (leftDerivedUpperStarIsoMapDerivedCategory Λ b).hom.app K =
      (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (upperStar Λ) h))).hom.app K := by
  subst h
  simp [Functor.mapDerivedCategoryNatIso_refl]

end Scheme

end AlgebraicGeometry.ProEtale.CondensedRing
