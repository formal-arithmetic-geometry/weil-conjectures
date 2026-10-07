/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Pushforward and pullback of pro-étale sheaves along an isomorphism

For an isomorphism of schemes `e : X ≅ Y`, the pushforwards `(e.hom)_*` and `(e.inv)_*` on
pro-étale sheaves are mutually inverse equivalences, by the identity and composition
isomorphisms `ProEtale.lowerStarId` and `ProEtale.lowerStarComp`. Consequently the pullback
`(e.hom)^*`, the left adjoint of `(e.hom)_*`, is the pushforward `(e.inv)_*` along the inverse.

Pushforwards are given by an explicit formula, `(g_* G)(V) = G(V ×_Y Z)`, and they are lax
monoidal; pullbacks are only characterised by their universal property. This is why the
Frobenius pullbacks of Weil sheaves (`WeilConjectures.WeilSheaf.Category`) are realised as
pushforwards along the inverse Frobenius.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStarCongr`: `g_* ≅ g'_*` for `g = g'`.
- `AlgebraicGeometry.ProEtale.lowerStarEquivalence`: the equivalence `(e.hom)_*` with inverse
  `(e.inv)_*`.
- `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`: `(e.hom)^* ≅ (e.inv)_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

/-- The pushforwards along equal morphisms are isomorphic. -/
noncomputable def lowerStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)_*[A] ≅ (g')_*[A] :=
  eqToIso (by rw [h])

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarCongr_rfl {Z Y : Scheme.{u}} {g : Z ⟶ Y} :
    lowerStarCongr A (rfl : g = g) = Iso.refl _ :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along the opposite of base change; the form of
`ProEtale.lowerStar_map_hom_app` at an object of the opposite site. -/
lemma lowerStar_map_hom_app' {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {G G' : Sheaf (ProEt.topology Z) A} (φ : G ⟶ G') (V : Y.ProEtᵒᵖ) :
    ((g)_*[A].map φ).hom.app V =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` are the
restriction maps along the pullback pasting isomorphisms. -/
lemma lowerStarComp_hom_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op := by
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_inv_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).inv.app V.unop).op := by
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `g_* ≅ g'_*` for `g = g'` are the restriction maps along the canonical
isomorphisms `V ×_{Y,g'} Z ≅ V ×_{Y,g} Z`. -/
lemma lowerStarCongr_hom_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A h).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).inv.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).inv.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

/-- The pullbacks along equal morphisms are isomorphic. -/
noncomputable def upperStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)^*[A] ≅ (g')^*[A] :=
  eqToIso (by rw [h])

variable {X Y : Scheme.{u}}

/-- The pushforward along an isomorphism `e : X ≅ Y` is an equivalence of categories of
pro-étale sheaves, with inverse the pushforward along `e.inv`. -/
noncomputable def lowerStarEquivalence (e : X ≅ Y) :
    Sheaf (ProEt.topology X) A ≌ Sheaf (ProEt.topology Y) A :=
  CategoryTheory.Equivalence.mk (e.hom)_*[A] (e.inv)_*[A]
    ((lowerStarId A X).symm ≪≫ lowerStarCongr A e.hom_inv_id.symm ≪≫
      (lowerStarComp A e.hom e.inv).symm)
    (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarEquivalence_functor (e : X ≅ Y) :
    (lowerStarEquivalence A e).functor = (e.hom)_*[A] :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarEquivalence_inverse (e : X ≅ Y) :
    (lowerStarEquivalence A e).inverse = (e.inv)_*[A] :=
  rfl

/-- The pullback along an isomorphism `e` is the pushforward along its inverse: both are left
adjoint to the pushforward `(e.hom)_*`. -/
noncomputable def upperStarIsoLowerStarInv (e : X ≅ Y) : (e.hom)^*[A] ≅ (e.inv)_*[A] :=
  (upperStarLowerStarAdjunction A e.hom).leftAdjointUniq
    (lowerStarEquivalence A e).symm.toAdjunction

variable {Z W : Scheme.{u}} (g : Z ⟶ W) [IsIso g]

instance isEquivalence_lowerStar : (g)_*[A].IsEquivalence :=
  (lowerStarEquivalence A (asIso g)).isEquivalence_functor

instance isEquivalence_upperStar : (g)^*[A].IsEquivalence :=
  Functor.isEquivalence_of_iso (upperStarIsoLowerStarInv A (asIso g)).symm

end ProEtale

end AlgebraicGeometry
