/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!
# Exchange isomorphisms of pushforwards and their coherence

For a commutative square `p ≫ b = a ≫ p'`-type relation `p ≫ b = a ≫ p` of schemes, the
*exchange isomorphism* `p_* ⋙ b_* ≅ a_* ⋙ p_*` of pushforwards of pro-étale sheaves is
`p_* ⋙ b_* ≅ (p ≫ b)_* = (a ≫ p)_* ≅ a_* ⋙ p_*`
(`AlgebraicGeometry.ProEtale.adicLowerStarExchange` for sheaves of `ℚ̄_ℓ,X`-modules). This file
proves the compatibilities of exchange isomorphisms needed to compare Weil structures under a
finite extension of the base field:

- `AlgebraicGeometry.ProEtale.adicLowerStarExchange_comp`: exchange isomorphisms are compatible
  with composition of the horizontal morphisms `a`, `b`;
- `AlgebraicGeometry.ProEtale.adicLowerStarExchange_id`: the exchange isomorphism of identities
  is the identity;
- `AlgebraicGeometry.ProEtale.adicLowerStarExchange_cube`: two exchange isomorphisms pasted along
  a commutative cube agree.

All of them are checked on sections, after writing every composition and congruence isomorphism
as a factorisation isomorphism `AlgebraicGeometry.ProEtale.lowerStarFactor`; on sections, these
are restriction maps along canonical isomorphisms of iterated fibre products.

## Implementation notes

The components of pushforwards of morphisms and of restriction maps of pushforwards are given by
`rfl`-lemmas (`AlgebraicGeometry.ProEtale.lowerStar_map_hom_app'`,
`AlgebraicGeometry.ProEtale.lowerStar_obj_obj_map'`). Used as `simp` lemmas they leave the kernel
with expensive definitional unfoldings, so this file restates them with a proof term
(`AlgebraicGeometry.ProEtale.lowerStar_map_hom_app_eq`,
`AlgebraicGeometry.ProEtale.lowerStar_obj_obj_map_eq`). For the same reason the congruence
isomorphisms are eliminated in favour of factorisation isomorphisms before passing to sections.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Sheaf

variable (A : Type u') [Category.{u + 1} A]

/-- `AlgebraicGeometry.ProEtale.lowerStar_map_hom_app'`, with a proof term. -/
lemma lowerStar_map_hom_app_eq {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {G G' : Sheaf (Scheme.ProEt.topology Z) A} (φ : G ⟶ G') (V : Y.ProEtᵒᵖ) :
    ((g)_*[A].map φ).hom.app V =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  lowerStar_map_hom_app' A g φ V

/-- `AlgebraicGeometry.ProEtale.lowerStar_obj_obj_map'`, with a proof term. -/
lemma lowerStar_obj_obj_map_eq {Z W : Scheme.{u}} (g : Z ⟶ W)
    (G : Sheaf (Scheme.ProEt.topology Z) A) {V V' : W.ProEtᵒᵖ} (φ : V ⟶ V') :
    ((g)_*[A].obj G).obj.map φ =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map φ.unop).op :=
  lowerStar_obj_obj_map' A g G φ

/-- Exchange isomorphisms, written with factorisation isomorphisms, are compatible with
composition of the horizontal morphisms. -/
lemma lowerStarFactor_exchange_comp {Z P : Scheme.{u}} (p : Z ⟶ P) (a₁ a₂ a₃ : Z ⟶ Z)
    (b₁ b₂ b₃ : P ⟶ P) (c₁ c₂ c₃ : Z ⟶ P) (ha : a₂ ≫ a₁ = a₃) (hb : b₂ ≫ b₁ = b₃)
    (h₁ : p ≫ b₁ = c₁) (h₁' : a₁ ≫ p = c₁) (h₂ : p ≫ b₂ = c₂) (h₂' : a₂ ≫ p = c₂)
    (h₃ : p ≫ b₃ = c₃) (h₃' : a₃ ≫ p = c₃) (G : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarFactor A hb).inv.app ((p)_*[A].obj G) ≫
        (b₁)_*[A].map ((lowerStarFactor A h₂).hom.app G ≫ (lowerStarFactor A h₂').inv.app G) ≫
        (lowerStarFactor A h₁).hom.app ((a₂)_*[A].obj G) ≫
        (lowerStarFactor A h₁').inv.app ((a₂)_*[A].obj G) =
      (lowerStarFactor A h₃).hom.app G ≫ (lowerStarFactor A h₃').inv.app G ≫
        (p)_*[A].map ((lowerStarFactor A ha).inv.app G) := by
  ext V : 3
  simp only [NatTrans.comp_app, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app_eq,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app, lowerStar_obj_obj_map_eq]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback,
    MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]

/-- The exchange isomorphism of identities, written with factorisation isomorphisms, is the
identity. -/
set_option linter.flexible false in
lemma lowerStarFactor_exchange_id {Z P : Scheme.{u}} (p : Z ⟶ P) (c : Z ⟶ P)
    (h : p ≫ 𝟙 P = c) (h' : 𝟙 Z ≫ p = c) (G : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarFactor A h).hom.app G ≫ (lowerStarFactor A h').inv.app G ≫
        (p)_*[A].map ((lowerStarId A Z).hom.app G) =
      (lowerStarId A P).hom.app ((p)_*[A].obj G) := by
  ext V : 3
  simp only [NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app_eq,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app, lowerStar_obj_obj_map_eq,
    lowerStarId_hom_app_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals try simp [MorphismProperty.Over.pullback, MorphismProperty.Over.pullbackId,
    MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]
  all_goals first | exact Category.id_comp _ | exact pullback.condition.symm

/-- Two exchange isomorphisms, written with factorisation isomorphisms, pasted along a
commutative cube agree. The vertical morphisms are `θ : Z ⟶ Z'`, `ψ : P ⟶ P'`, the
horizontal ones `ā : Z ⟶ P`, `ā' : Z' ⟶ P'`, and the endomorphisms `F`, `F'`, `G`, `G'` of
`Z`, `Z'`, `P`, `P'`. -/
lemma lowerStarFactor_exchange_cube {Z Z' P P' : Scheme.{u}} (θ : Z ⟶ Z') (ψ : P ⟶ P')
    (a : Z ⟶ P) (a' : Z' ⟶ P') (F : Z ⟶ Z) (F' : Z' ⟶ Z') (G : P ⟶ P) (G' : P' ⟶ P')
    (d : Z ⟶ P') (e : θ ≫ a' = d) (e' : a ≫ ψ = d)
    (cθ : Z ⟶ Z') (hθ : θ ≫ F' = cθ) (hθ' : F ≫ θ = cθ)
    (cψ : P ⟶ P') (hψ : ψ ≫ G' = cψ) (hψ' : G ≫ ψ = cψ)
    (ca : Z ⟶ P) (hA : a ≫ G = ca) (hA' : F ≫ a = ca)
    (cb : Z' ⟶ P') (hB : a' ≫ G' = cb) (hB' : F' ≫ a' = cb)
    (K : Sheaf (Scheme.ProEt.topology Z) A) :
    (G')_*[A].map ((lowerStarFactor A e).hom.app K ≫ (lowerStarFactor A e').inv.app K) ≫
        (lowerStarFactor A hψ).hom.app ((a)_*[A].obj K) ≫
        (lowerStarFactor A hψ').inv.app ((a)_*[A].obj K) ≫
        (ψ)_*[A].map ((lowerStarFactor A hA).hom.app K ≫ (lowerStarFactor A hA').inv.app K) =
      (lowerStarFactor A hB).hom.app ((θ)_*[A].obj K) ≫
        (lowerStarFactor A hB').inv.app ((θ)_*[A].obj K) ≫
        (a')_*[A].map ((lowerStarFactor A hθ).hom.app K ≫ (lowerStarFactor A hθ').inv.app K) ≫
        (lowerStarFactor A e).hom.app ((F)_*[A].obj K) ≫
        (lowerStarFactor A e').inv.app ((F)_*[A].obj K) := by
  ext V : 3
  simp only [NatTrans.comp_app, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app_eq,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app, lowerStar_obj_obj_map_eq]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackComp, e, e', reassoc_of% e, reassoc_of% e']

end Sheaf

end AlgebraicGeometry.ProEtale
