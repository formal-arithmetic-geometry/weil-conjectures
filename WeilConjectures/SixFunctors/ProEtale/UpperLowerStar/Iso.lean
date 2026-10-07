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
- `AlgebraicGeometry.ProEtale.upperStarCompIso`: `a^* ∘ b^* ≅ c^* ∘ d^*` for `a ≫ b = c ≫ d`.
- `AlgebraicGeometry.ProEtale.lowerStarEquivalence`: the equivalence `(e.hom)_*` with inverse
  `(e.inv)_*`.
- `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`: `(e.hom)^* ≅ (e.inv)_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

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

/-- The pullbacks along equal morphisms are isomorphic. -/
noncomputable def upperStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)^*[A] ≅ (g')^*[A] :=
  eqToIso (by rw [h])

/-- The pullbacks along the two sides of a commutative square `a ≫ b = c ≫ d` agree:
`a^* ∘ b^* ≅ (a ≫ b)^* = (c ≫ d)^* ≅ c^* ∘ d^*`. -/
noncomputable def upperStarCompIso {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) :
    (b)^*[A] ⋙ (a)^*[A] ≅ (d)^*[A] ⋙ (c)^*[A] :=
  (upperStarComp A a b).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A c d

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
