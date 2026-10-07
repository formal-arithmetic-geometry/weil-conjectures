/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# The divisor map on the small étale site

Let `X` be an irreducible scheme with generic point `i : Spec k(X) ⟶ X`. The sections of the
étale sheaf `i_* 𝔾ₘ` over an étale `X`-scheme `V` are the units of `Γ(V ×_X Spec k(X), 𝒪)`, the
rational functions on `V` which are invertible on its generic fibre. This file defines the
order of vanishing of such a function at a point `y` of `V` lying over a point of `X` of
codimension one, and assembles these orders into the *divisor map*

```
  i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ)),   f ↦ (y ↦ ord_y f)
```

with values in the étale sheaf of functions on points
(`AlgebraicGeometry.Scheme.pointFunctionSheaf`).

The order at `y` is computed in the *local generic ring*
`Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)`, the ring of functions on the generic fibre of the local
scheme of `V` at `y`; when `X` is regular, `𝒪_{V,y}` is a discrete valuation ring and the local
generic ring is its fraction field.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.localGenericRing`: the ring `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)`.
- `AlgebraicGeometry.Scheme.Etale.ord`: the order of vanishing at `y` of a function on the
  generic fibre of `V`.
- `AlgebraicGeometry.Scheme.divisorMap`: the divisor map `i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Order

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IrreducibleSpace X]

namespace Etale

/-- The local generic ring `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` of an étale `X`-scheme `V` at a
point `y`: the ring of functions on the generic fibre of the local scheme of `V` at `y`. -/
noncomputable def localGenericRing (V : X.Etale) (y : V.left) : CommRingCat.{u} :=
  Γ(pullback (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField, ⊤)

/-- The map `𝒪_{V,y} ⟶ Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` from the local ring to the local
generic ring. -/
noncomputable def stalkToLocalGenericRing (V : X.Etale) (y : V.left) :
    V.left.presheaf.stalk y ⟶ localGenericRing V y :=
  (Scheme.ΓSpecIso _).inv ≫
    (pullback.fst (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField).appTop

/-- The map `Γ(V ×_X Spec k(X), 𝒪) ⟶ Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` restricting a function
on the generic fibre of `V` to the generic fibre of the local scheme at `y`. -/
noncomputable def toLocalGenericRing (V : X.Etale) (y : V.left) :
    Γ(pullback V.hom X.fromSpecFunctionField, ⊤) ⟶ localGenericRing V y :=
  (pullback.map _ _ _ _ (V.left.fromSpecStalk y) (𝟙 _) (𝟙 _) (by simp) (by simp)).appTop

open Classical in
/-- The order of vanishing at a point `y` of an étale `X`-scheme `V` of a function `f` on the
generic fibre `V ×_X Spec k(X)`. It is computed in the local generic ring at `y`, with
`Ring.ordOf` relative to the local ring `𝒪_{V,y}`, if `y` lies over a point of `X` of
codimension one, and is `0` otherwise. -/
noncomputable def ord (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) : ℤ :=
  if coheight (V.hom y) = 1 then
    letI := (stalkToLocalGenericRing V y).hom.toAlgebra
    Ring.ordOf (V.left.presheaf.stalk y) (localGenericRing V y) (toLocalGenericRing V y f)
  else 0

lemma ord_of_coheight_ne_one (V : X.Etale) {y : V.left} (hy : coheight (V.hom y) ≠ 1)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) : ord V y f = 0 :=
  if_neg hy

/-- The order of vanishing is additive on units. -/
lemma ord_mul (V : X.Etale) (y : V.left) (f g : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) :
    ord V y ↑(f * g) = ord V y f + ord V y g := by
  by_cases hy : coheight (V.hom y) = 1
  · simp only [ord, if_pos hy]
    let := (stalkToLocalGenericRing V y).hom.toAlgebra
    have := Ring.ordOf_mul (R := V.left.presheaf.stalk y)
      (Units.map (toLocalGenericRing V y).hom.toMonoidHom f)
      (Units.map (toLocalGenericRing V y).hom.toMonoidHom g)
    simpa using this
  · rw [ord_of_coheight_ne_one _ hy, ord_of_coheight_ne_one _ hy, ord_of_coheight_ne_one _ hy,
      add_zero]

lemma ord_one (V : X.Etale) (y : V.left) : ord V y 1 = 0 := by
  have := ord_mul V y 1 1
  simp only [mul_one, Units.val_one] at this
  omega

/-- The restriction to the local generic ring of a function on `V` is its germ, mapped into
the local generic ring. -/
lemma toLocalGenericRing_fst_appTop (V : X.Etale) (y : V.left) (a : Γ(V.left, ⊤)) :
    toLocalGenericRing V y ((pullback.fst V.hom X.fromSpecFunctionField).appTop a) =
      stalkToLocalGenericRing V y (V.left.presheaf.germ ⊤ y trivial a) := by
  have h : (pullback.fst V.hom X.fromSpecFunctionField).appTop ≫ toLocalGenericRing V y =
      V.left.presheaf.germ ⊤ y trivial ≫ stalkToLocalGenericRing V y := by
    rw [toLocalGenericRing, ← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.comp_appTop,
      fromSpecStalk_appTop, stalkToLocalGenericRing]
    simp
  exact congrArg (fun f ↦ f a) (congrArg CommRingCat.Hom.hom h)

/-- A unit on `V` has order `0` at every point. -/
lemma ord_fst_appTop (V : X.Etale) (y : V.left) (u : Γ(V.left, ⊤)ˣ) :
    ord V y ((pullback.fst V.hom X.fromSpecFunctionField).appTop u.val) = 0 := by
  by_cases hy : coheight (V.hom y) = 1
  · rw [ord, if_pos hy, toLocalGenericRing_fst_appTop]
    let := (stalkToLocalGenericRing V y).hom.toAlgebra
    by_cases h : (IsNoetherianRing (V.left.presheaf.stalk y) ∧
        Ring.KrullDimLE 1 (V.left.presheaf.stalk y) ∧ IsDomain (V.left.presheaf.stalk y)) ∧
        IsFractionRing (V.left.presheaf.stalk y) (localGenericRing V y)
    · have := h.1.1; have := h.1.2.1; have := h.1.2.2; have := h.2
      exact Ring.ordOf_algebraMap_of_isUnit (u.isUnit.map _)
    · rw [Ring.ordOf, dif_neg h]
  · exact ord_of_coheight_ne_one V hy _

/-- The order of vanishing at the points of `V`, as an additive map from the units on the
generic fibre of `V`, written additively, to the functions `V → ℤ`. -/
noncomputable def ordHom (V : X.Etale) :
    Additive (Γ(pullback V.hom X.fromSpecFunctionField, ⊤))ˣ →+ (V.left → ULift.{u + 1} ℤ) where
  toFun f y := ULift.up (ord V y (Additive.toMul f).val)
  map_zero' := by
    funext y
    exact ULift.ext _ _ (ord_one V y)
  map_add' f g := by
    funext y
    exact ULift.ext _ _ (ord_mul V y _ _)

/-- **Naturality of the order of vanishing.** For a morphism `φ : W ⟶ V` of étale
`X`-schemes, a point `y` of `W` and a unit `f` on the generic fibre of `V`, the order of the
pullback of `f` at `y` is the order of `f` at `φ y`. When `X` is regular the local rings
`𝒪_{V,φ y} ⟶ 𝒪_{W,y}` are discrete valuation rings and the étale map is unramified, so a
uniformiser stays a uniformiser (`Ring.ordOf_map`). The proof is `sorry`. -/
lemma ord_map {V W : X.Etale} (φ : W ⟶ V) (y : W.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) :
    ord W y (((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
      φ).left.appTop f.val) = ord V (φ.left y) f := by
  sorry

end Etale

variable (X)

/-- **The divisor map.** For an irreducible scheme `X` with generic point
`i : Spec k(X) ⟶ X`, the map of étale sheaves `i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ))` sending a unit `f` on
the generic fibre of an étale `X`-scheme `V` to the function `y ↦ ord_y f` of orders of
vanishing at the points of `V` over codimension one points of `X`. -/
noncomputable def divisorMap :
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
        (Spec X.functionField).gmSheaf ⟶
      X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  ⟨{ app V := AddCommGrpCat.ofHom ((Etale.ordHom V.unop).comp AddEquiv.ulift.toAddMonoidHom)
     naturality {V W} φ := by
      ext f
      funext y
      exact ULift.ext _ _ (Etale.ord_map φ.unop y _) }⟩

end AlgebraicGeometry.Scheme
