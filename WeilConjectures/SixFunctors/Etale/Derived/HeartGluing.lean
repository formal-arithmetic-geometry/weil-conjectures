/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Gluing morphisms between sheaves placed in degree zero

Morphisms `F[0] ⟶ G[0]` in `D(X_ét, Λ)` between étale sheaves placed in degree zero are
morphisms of sheaves `F ⟶ G`, and morphisms of sheaves glue along open covers: the presheaf
`V ↦ Hom(F|_V, G|_V)` is a sheaf. So morphisms `K ⟶ M` between objects of `D(X_ét, Λ)` that are
isomorphic to sheaves in degree zero can be glued from morphisms `Le_j^* K ⟶ Le_j^* M` on the
members `e_j : V_j ⟶ X` of an open cover which agree on overlaps.

## Main statements

- `AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- **Gluing morphisms in the heart.** Let `K` and `M` be objects of `D(X_ét, Λ)` isomorphic to
sheaves `F` and `G` placed in degree zero, and let `e_j : V_j ⟶ X` be open immersions covering
`X`. Morphisms `δ_j : Le_j^* K ⟶ Le_j^* M` which agree after restriction to every open `W`
lying over two members of the cover glue to a morphism `γ : K ⟶ M` with `Le_j^* γ = δ_j`.

Through `K ≅ F[0]` and `M ≅ G[0]`, and `Le^* (F[0]) ≅ (e^* F)[0]`, this is the gluing of
morphisms of étale sheaves `e_j^* F ⟶ e_j^* G` along the open cover: the sheaf property of the
presheaf `V ↦ Hom(F|_V, G|_V)` on `X_ét` (`CategoryTheory.Presheaf.IsSheaf.hom`). -/
theorem exists_hom_of_isOpenImmersion_cover
    {K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (_eK : K ≅ (DerivedCategory.singleFunctor _ 0).obj F)
    (_eM : M ≅ (DerivedCategory.singleFunctor _ 0).obj G)
    {ι : Type u} {V : ι → Scheme.{u}} (e : ∀ j, V j ⟶ X) [∀ j, IsOpenImmersion (e j)]
    (_hcov : ∀ x : X, ∃ j, x ∈ Set.range (e j).base)
    (δ : ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((e j)^*[ModuleCat.{u + 1} Λ])).obj M)
    (_hδ : ∀ j k {W : Scheme.{u}} (a : W ⟶ V j) (b : W ⟶ V k) [IsOpenImmersion a]
      [IsOpenImmersion b] (h : a ≫ e j = b ≫ e k),
      (leftDerivedUpperStarComp _ a (e j)).hom.app K ≫ (L((a)^*[_])).map (δ j) ≫
          (leftDerivedUpperStarComp _ a (e j)).inv.app M =
        (leftDerivedUpperStarComp _ b (e k) (a ≫ e j) h).hom.app K ≫ (L((b)^*[_])).map (δ k) ≫
          (leftDerivedUpperStarComp _ b (e k) (a ≫ e j) h).inv.app M) :
    ∃ γ : K ⟶ M, ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).map γ = δ j :=
  sorry

end Etale

end AlgebraicGeometry
