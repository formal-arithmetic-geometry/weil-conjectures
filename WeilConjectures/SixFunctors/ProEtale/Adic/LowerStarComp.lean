/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module

/-!
# Composition of pushforwards and exchange isomorphisms

For commutative squares `p ≫ a₂ = a₁ ≫ p` of schemes, the exchange isomorphisms
`p_* ⋙ a₂_* ≅ a₁_* ⋙ p_*` of pushforwards of pro-étale sheaves are compatible with the
composition isomorphisms `p_* ⋙ q_* ≅ (p ≫ q)_*`, both for sheaves with values in a category
`A` and for sheaves of `ℚ̄_ℓ,X`-modules.

## Main statements

- `AlgebraicGeometry.ProEtale.lowerStarComp_exchange`: compatibility for sheaves with values
  in `A`.
- `AlgebraicGeometry.ProEtale.adicLowerStarComp_exchange`: compatibility for sheaves of
  `ℚ̄_ℓ,X`-modules.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_hom_app_lowerStar_obj_hom_app {R S T W : Scheme.{u}} (g : W ⟶ T)
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) (G : Sheaf (Scheme.ProEt.topology W) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).hom.app ((g)_*[A].obj G)).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop)).op :=
  lowerStarComp_hom_app_hom_app A h₁ h₂ _ V

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_inv_app_lowerStar_obj_hom_app {R S T W : Scheme.{u}} (g : W ⟶ T)
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) (G : Sheaf (Scheme.ProEt.topology W) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).inv.app ((g)_*[A].obj G)).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.pullbackComp h₁ h₂).inv.app V.unop)).op :=
  lowerStarComp_inv_app_hom_app A h₁ h₂ _ V

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarCongr_hom_app_lowerStar_obj_hom_app {Z Y W : Scheme.{u}} (g : W ⟶ Z)
    {h h' : Z ⟶ Y} (e : h = h') (G : Sheaf (Scheme.ProEt.topology W) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A e).hom.app ((g)_*[A].obj G)).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.pullbackCongr e).inv.app V.unop)).op :=
  lowerStarCongr_hom_app_hom_app A e _ V

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The exchange isomorphisms `p_* ⋙ a₂_* ≅ a₁_* ⋙ p_*` of pushforwards along commutative
squares `p ≫ a₂ = a₁ ≫ p` are compatible with composition of pushforwards. Writing `ex` for
the exchange isomorphisms of the squares `p ≫ a₂ = a₁ ≫ p`, `q ≫ a₃ = a₂ ≫ q` and
`(p ≫ q) ≫ a₃ = a₁ ≫ (p ≫ q)`, and `c` for `q_* p_* ≅ (p ≫ q)_*`, the diagram
```
a₃_* q_* p_* G ------------c------------> a₃_* (p ≫ q)_* G
      |                                          |
      ex                                         ex
      v                                          v
q_* a₂_* p_* G --q_* ex--> q_* p_* a₁_* G --c--> (p ≫ q)_* a₁_* G
```
commutes. -/
lemma lowerStarComp_exchange {T₁ T₂ T₃ : Scheme.{u}} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (a₁ : T₁ ⟶ T₁) (a₂ : T₂ ⟶ T₂) (a₃ : T₃ ⟶ T₃) (h₁ : p ≫ a₂ = a₁ ≫ p) (h₂ : q ≫ a₃ = a₂ ≫ q)
    (h₁₂ : (p ≫ q) ≫ a₃ = a₁ ≫ (p ≫ q)) (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (a₃)_*[A].map ((lowerStarComp A p q).hom.app G) ≫
        (lowerStarComp A (p ≫ q) a₃).hom.app G ≫ (lowerStarCongr A h₁₂).hom.app G ≫
          (lowerStarComp A a₁ (p ≫ q)).inv.app G =
      (lowerStarComp A q a₃).hom.app ((p)_*[A].obj G) ≫
        (lowerStarCongr A h₂).hom.app ((p)_*[A].obj G) ≫
          (lowerStarComp A a₂ q).inv.app ((p)_*[A].obj G) ≫
            (q)_*[A].map ((lowerStarComp A p a₂).hom.app G ≫ (lowerStarCongr A h₁).hom.app G ≫
              (lowerStarComp A a₁ p).inv.app G) ≫
              (lowerStarComp A p q).hom.app ((a₁)_*[A].obj G) := by
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
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk]
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk]
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `AlgebraicGeometry.ProEtale.lowerStarComp_exchange` for a morphism `r` equal to `p ≫ q`. -/
lemma lowerStarComp_exchange' {T₁ T₂ T₃ : Scheme.{u}} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (r : T₁ ⟶ T₃) (hr : p ≫ q = r)
    (a₁ : T₁ ⟶ T₁) (a₂ : T₂ ⟶ T₂) (a₃ : T₃ ⟶ T₃) (h₁ : p ≫ a₂ = a₁ ≫ p) (h₂ : q ≫ a₃ = a₂ ≫ q)
    (h₁₃ : r ≫ a₃ = a₁ ≫ r) (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (a₃)_*[A].map ((lowerStarComp A p q).hom.app G ≫ (lowerStarCongr A hr).hom.app G) ≫
        (lowerStarComp A r a₃).hom.app G ≫ (lowerStarCongr A h₁₃).hom.app G ≫
          (lowerStarComp A a₁ r).inv.app G =
      (lowerStarComp A q a₃).hom.app ((p)_*[A].obj G) ≫
        (lowerStarCongr A h₂).hom.app ((p)_*[A].obj G) ≫
          (lowerStarComp A a₂ q).inv.app ((p)_*[A].obj G) ≫
            (q)_*[A].map ((lowerStarComp A p a₂).hom.app G ≫ (lowerStarCongr A h₁).hom.app G ≫
              (lowerStarComp A a₁ p).inv.app G) ≫
              (lowerStarComp A p q).hom.app ((a₁)_*[A].obj G) ≫
                (lowerStarCongr A hr).hom.app ((a₁)_*[A].obj G) := by
  subst hr
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact lowerStarComp_exchange A p q a₁ a₂ a₃ h₁ h₂ h₁₃ G

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1600000 in
-- the `Mod`-level composites unfold to the underlying sheaf-level ones
/-- `AlgebraicGeometry.ProEtale.lowerStarComp_exchange'` for sheaves of `ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStarComp_exchange {T₁ T₂ T₃ : Scheme.{u}} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (r : T₁ ⟶ T₃) (hr : p ≫ q = r)
    (a₁ : T₁ ⟶ T₁) (a₂ : T₂ ⟶ T₂) (a₃ : T₃ ⟶ T₃) (h₁ : p ≫ a₂ = a₁ ≫ p) (h₂ : q ≫ a₃ = a₂ ≫ q)
    (h₁₃ : r ≫ a₃ = a₁ ≫ r) (M : AdicSheaf l T₁) :
    (a₃)_*ᵃ[l].map ((adicLowerStarComp l p q).hom.app M ≫ (adicLowerStarCongr l hr).hom.app M) ≫
        (adicLowerStarComp l r a₃).hom.app M ≫ (adicLowerStarCongr l h₁₃).hom.app M ≫
          (adicLowerStarComp l a₁ r).inv.app M =
      (adicLowerStarComp l q a₃).hom.app ((p)_*ᵃ[l].obj M) ≫
        (adicLowerStarCongr l h₂).hom.app ((p)_*ᵃ[l].obj M) ≫
          (adicLowerStarComp l a₂ q).inv.app ((p)_*ᵃ[l].obj M) ≫
            (q)_*ᵃ[l].map ((adicLowerStarComp l p a₂).hom.app M ≫
              (adicLowerStarCongr l h₁).hom.app M ≫ (adicLowerStarComp l a₁ p).inv.app M) ≫
              (adicLowerStarComp l p q).hom.app ((a₁)_*ᵃ[l].obj M) ≫
                (adicLowerStarCongr l hr).hom.app ((a₁)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom]
  exact lowerStarComp_exchange' (WeilCoefficients.{u} l) p q r hr a₁ a₂ a₃ h₁ h₂ h₁₃ M.X

end ProEtale

end AlgebraicGeometry
