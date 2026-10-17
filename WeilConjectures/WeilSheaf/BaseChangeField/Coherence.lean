/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# Coherence of exchange isomorphisms of pushforwards

For a commutative square `p ≫ a' = a ≫ p` of schemes, the *exchange isomorphism*
`p_* ⋙ a'_* ≅ a_* ⋙ p_*` is the composite `p_* a'_* ≅ (p ≫ a')_* = (a ≫ p)_* ≅ a_* p_*` of the
composition isomorphisms of pushforwards. This file proves the compatibilities of exchange
isomorphisms that are needed to transport Weil structures along isomorphisms of geometric
fibers: with the identity (`AlgebraicGeometry.ProEtale.adicLowerStar_exchange_id`), with the
composition of the vertical sides (`AlgebraicGeometry.ProEtale.adicLowerStar_exchange_vcomp`)
and with a commutative cube (`AlgebraicGeometry.ProEtale.adicLowerStar_exchange_cube`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {T₁ T₂ : Scheme.{u}} (p : T₁ ⟶ T₂)

/-- The exchange isomorphism along `p` of pushforwards along squares whose vertical sides are
the identity, up to `lowerStarId`. -/
lemma lowerStar_exchange_id {a : T₁ ⟶ T₁} {a' : T₂ ⟶ T₂} (ha : a = 𝟙 T₁) (ha' : a' = 𝟙 T₂)
    (h : p ≫ a' = a ≫ p) (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (lowerStarCongr A ha').hom.app ((p)_*[A].obj G) ≫ (lowerStarId A T₂).hom.app _ =
      (lowerStarComp A p a').hom.app G ≫ (lowerStarCongr A h).hom.app G ≫
        (lowerStarComp A a p).inv.app G ≫
          (p)_*[A].map ((lowerStarCongr A ha).hom.app G ≫ (lowerStarId A T₁).hom.app G) := by
  subst ha ha'
  ext V : 3
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_obj_obj_map']
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  (repeat' apply pullback.hom_ext) <;>
    simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]

/-- The exchange isomorphisms along `p` are compatible with the composition `c = x ≫ y` of the
vertical sides: the exchange isomorphism of the square of `c` is the composite of those of the
squares of `x` and of `y`, up to the composition isomorphisms of pushforwards. -/
lemma lowerStar_exchange_vcomp {x₁ y₁ c₁ : T₁ ⟶ T₁} {x₂ y₂ c₂ : T₂ ⟶ T₂}
    (hc₁ : c₁ = x₁ ≫ y₁) (hc₂ : c₂ = x₂ ≫ y₂) (hx : p ≫ x₂ = x₁ ≫ p) (hy : p ≫ y₂ = y₁ ≫ p)
    (hc : p ≫ c₂ = c₁ ≫ p) (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (lowerStarCongr A hc₂).hom.app ((p)_*[A].obj G) ≫
        (lowerStarComp A x₂ y₂).inv.app ((p)_*[A].obj G) ≫
        (y₂)_*[A].map ((lowerStarComp A p x₂).hom.app G ≫ (lowerStarCongr A hx).hom.app G ≫
          (lowerStarComp A x₁ p).inv.app G) ≫
        (lowerStarComp A p y₂).hom.app ((x₁)_*[A].obj G) ≫
        (lowerStarCongr A hy).hom.app ((x₁)_*[A].obj G) ≫
        (lowerStarComp A y₁ p).inv.app ((x₁)_*[A].obj G) =
      (lowerStarComp A p c₂).hom.app G ≫ (lowerStarCongr A hc).hom.app G ≫
        (lowerStarComp A c₁ p).inv.app G ≫
        (p)_*[A].map ((lowerStarCongr A hc₁).hom.app G ≫ (lowerStarComp A x₁ y₁).inv.app G) := by
  ext V : 3
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_lowerStar_obj_hom_app,
    lowerStarComp_inv_app_lowerStar_obj_hom_app, lowerStarCongr_hom_app_lowerStar_obj_hom_app]
  simp only [lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  (repeat' apply pullback.hom_ext) <;>
    simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]

/-- The exchange isomorphisms of the faces of a commutative cube are compatible: for a square
`p ≫ t₂ = t₁ ≫ p'` and vertical endomorphisms `x₁, x₂, y₁, y₂` of its corners forming
commutative squares with `p`, `p'`, `t₁` and `t₂`, the two composites of exchange isomorphisms
`y₂_* t₂_* p_* ⟶ p'_* t₁_* x₁_*` agree. -/
lemma lowerStar_exchange_cube {T₁' T₂' : Scheme.{u}} (p' : T₁' ⟶ T₂') (t₁ : T₁ ⟶ T₁')
    (t₂ : T₂ ⟶ T₂') {x₁ : T₁ ⟶ T₁} {x₂ : T₂ ⟶ T₂} {y₁ : T₁' ⟶ T₁'} {y₂ : T₂' ⟶ T₂'}
    (hc : p ≫ t₂ = t₁ ≫ p') (hp : p ≫ x₂ = x₁ ≫ p) (hp' : p' ≫ y₂ = y₁ ≫ p')
    (ht₁ : t₁ ≫ y₁ = x₁ ≫ t₁) (ht₂ : t₂ ≫ y₂ = x₂ ≫ t₂)
    (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (y₂)_*[A].map ((lowerStarComp A p t₂).hom.app G ≫ (lowerStarCongr A hc).hom.app G ≫
        (lowerStarComp A t₁ p').inv.app G) ≫
      (lowerStarComp A p' y₂).hom.app ((t₁)_*[A].obj G) ≫
        (lowerStarCongr A hp').hom.app ((t₁)_*[A].obj G) ≫
        (lowerStarComp A y₁ p').inv.app ((t₁)_*[A].obj G) ≫
      (p')_*[A].map ((lowerStarComp A t₁ y₁).hom.app G ≫ (lowerStarCongr A ht₁).hom.app G ≫
        (lowerStarComp A x₁ t₁).inv.app G) =
    (lowerStarComp A t₂ y₂).hom.app ((p)_*[A].obj G) ≫
        (lowerStarCongr A ht₂).hom.app ((p)_*[A].obj G) ≫
        (lowerStarComp A x₂ t₂).inv.app ((p)_*[A].obj G) ≫
      (t₂)_*[A].map ((lowerStarComp A p x₂).hom.app G ≫ (lowerStarCongr A hp).hom.app G ≫
        (lowerStarComp A x₁ p).inv.app G) ≫
      (lowerStarComp A p t₂).hom.app ((x₁)_*[A].obj G) ≫
        (lowerStarCongr A hc).hom.app ((x₁)_*[A].obj G) ≫
        (lowerStarComp A t₁ p').inv.app ((x₁)_*[A].obj G) := by
  ext V : 3
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_lowerStar_obj_hom_app,
    lowerStarComp_inv_app_lowerStar_obj_hom_app, lowerStarCongr_hom_app_lowerStar_obj_hom_app]
  simp only [lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  (repeat' apply pullback.hom_ext) <;>
    simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]

end

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ : Scheme.{u}} (p : T₁ ⟶ T₂)

/-- `AlgebraicGeometry.ProEtale.lowerStar_exchange_id` for sheaves of `ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStar_exchange_id {a : T₁ ⟶ T₁} {a' : T₂ ⟶ T₂} (ha : a = 𝟙 T₁) (ha' : a' = 𝟙 T₂)
    (h : p ≫ a' = a ≫ p) (M : AdicSheaf l T₁) :
    (adicLowerStarCongr l ha').hom.app ((p)_*ᵃ[l].obj M) ≫ (adicLowerStarId l T₂).hom.app _ =
      (adicLowerStarComp l p a').hom.app M ≫ (adicLowerStarCongr l h).hom.app M ≫
        (adicLowerStarComp l a p).inv.app M ≫
          (p)_*ᵃ[l].map ((adicLowerStarCongr l ha).hom.app M ≫
            (adicLowerStarId l T₁).hom.app M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarId_hom_app_hom]
  exact lowerStar_exchange_id (WeilCoefficients.{u} l) p ha ha' h M.X

/-- `AlgebraicGeometry.ProEtale.lowerStar_exchange_vcomp` for sheaves of `ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStar_exchange_vcomp {x₁ y₁ c₁ : T₁ ⟶ T₁} {x₂ y₂ c₂ : T₂ ⟶ T₂}
    (hc₁ : c₁ = x₁ ≫ y₁) (hc₂ : c₂ = x₂ ≫ y₂) (hx : p ≫ x₂ = x₁ ≫ p) (hy : p ≫ y₂ = y₁ ≫ p)
    (hc : p ≫ c₂ = c₁ ≫ p) (M : AdicSheaf l T₁) :
    (adicLowerStarCongr l hc₂).hom.app ((p)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l x₂ y₂).inv.app ((p)_*ᵃ[l].obj M) ≫
        (y₂)_*ᵃ[l].map ((adicLowerStarComp l p x₂).hom.app M ≫
          (adicLowerStarCongr l hx).hom.app M ≫ (adicLowerStarComp l x₁ p).inv.app M) ≫
        (adicLowerStarComp l p y₂).hom.app ((x₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarCongr l hy).hom.app ((x₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l y₁ p).inv.app ((x₁)_*ᵃ[l].obj M) =
      (adicLowerStarComp l p c₂).hom.app M ≫ (adicLowerStarCongr l hc).hom.app M ≫
        (adicLowerStarComp l c₁ p).inv.app M ≫
        (p)_*ᵃ[l].map ((adicLowerStarCongr l hc₁).hom.app M ≫
          (adicLowerStarComp l x₁ y₁).inv.app M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom]
  exact lowerStar_exchange_vcomp (WeilCoefficients.{u} l) p hc₁ hc₂ hx hy hc M.X

/-- `AlgebraicGeometry.ProEtale.lowerStar_exchange_cube` for sheaves of `ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStar_exchange_cube {T₁' T₂' : Scheme.{u}} (p' : T₁' ⟶ T₂') (t₁ : T₁ ⟶ T₁')
    (t₂ : T₂ ⟶ T₂') {x₁ : T₁ ⟶ T₁} {x₂ : T₂ ⟶ T₂} {y₁ : T₁' ⟶ T₁'} {y₂ : T₂' ⟶ T₂'}
    (hc : p ≫ t₂ = t₁ ≫ p') (hp : p ≫ x₂ = x₁ ≫ p) (hp' : p' ≫ y₂ = y₁ ≫ p')
    (ht₁ : t₁ ≫ y₁ = x₁ ≫ t₁) (ht₂ : t₂ ≫ y₂ = x₂ ≫ t₂) (M : AdicSheaf l T₁) :
    (y₂)_*ᵃ[l].map ((adicLowerStarComp l p t₂).hom.app M ≫ (adicLowerStarCongr l hc).hom.app M ≫
        (adicLowerStarComp l t₁ p').inv.app M) ≫
      (adicLowerStarComp l p' y₂).hom.app ((t₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarCongr l hp').hom.app ((t₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l y₁ p').inv.app ((t₁)_*ᵃ[l].obj M) ≫
      (p')_*ᵃ[l].map ((adicLowerStarComp l t₁ y₁).hom.app M ≫
        (adicLowerStarCongr l ht₁).hom.app M ≫ (adicLowerStarComp l x₁ t₁).inv.app M) =
    (adicLowerStarComp l t₂ y₂).hom.app ((p)_*ᵃ[l].obj M) ≫
        (adicLowerStarCongr l ht₂).hom.app ((p)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l x₂ t₂).inv.app ((p)_*ᵃ[l].obj M) ≫
      (t₂)_*ᵃ[l].map ((adicLowerStarComp l p x₂).hom.app M ≫
        (adicLowerStarCongr l hp).hom.app M ≫ (adicLowerStarComp l x₁ p).inv.app M) ≫
      (adicLowerStarComp l p t₂).hom.app ((x₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarCongr l hc).hom.app ((x₁)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l t₁ p').inv.app ((x₁)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom]
  exact lowerStar_exchange_cube (WeilCoefficients.{u} l) p p' t₁ t₂ hc hp hp' ht₁ ht₂ M.X

end AlgebraicGeometry.ProEtale
