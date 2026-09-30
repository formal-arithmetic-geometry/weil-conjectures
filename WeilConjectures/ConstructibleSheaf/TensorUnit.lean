/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# The constant sheaf `Λ` as the monoidal unit

The monoidal unit `𝟙_` of étale sheaves of `Λ`-modules is the constant sheaf `Λ`
(definitionally `constantSheaf` applied to `ModuleCat.of Λ Λ`), so the pullback of constant
sheaves `AlgebraicGeometry.Scheme.upperStarConstantSheafIso` applies to it.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarTensorUnitIso`: the isomorphism `g^* Λ ≅ Λ`.
- `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`: for `f : Y ⟶ X` and
  `g : Y ⟶ Y` with `g ≫ f = f`, the endomorphism of `f_* Λ` given by pulling back sections
  along `g`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The pullback of étale sheaves of `Λ`-modules along `g : Y ⟶ X` preserves the monoidal
unit, the constant sheaf `Λ`: `g^* Λ ≅ Λ`. -/
def upperStarTensorUnitIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (g)^*[ModuleCat Λ].obj (𝟙_ _) ≅ 𝟙_ _ :=
  -- the unit is definitionally `constantSheaf` applied to `ModuleCat.of Λ Λ`
  (Scheme.upperStarConstantSheafIso _ g).app (ModuleCat.of Λ Λ)

variable {Λ}

/-- For `f : Y ⟶ X` and an endomorphism `g : Y ⟶ Y` over `X`, the endomorphism of `f_* Λ`
pulling back sections along `g`: `f_*` of the unit of `g^* ⊣ g_*`, followed by the
composition isomorphism of pushforwards,

```
f_* Λ --f_* η--> f_* g_* g^* Λ ≅ f_* g_* Λ ≅ (g ≫ f)_* Λ = f_* Λ
```
-/
def lowerStarConstantSheafEndOfOver {X Y : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ Y)
    (h : g ≫ f = f) :
    (f)_*[ModuleCat Λ].obj (𝟙_ _) ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _) :=
  (f)_*[ModuleCat Λ].map ((upperStarLowerStarAdjunction _ g).unit.app _ ≫
      (g)_*[ModuleCat Λ].map (upperStarTensorUnitIso Λ g).hom) ≫
    (lowerStarComp _ g f f h.symm).hom.app _

/-- The identity of `Y` acts trivially on `f_* Λ`. -/
lemma lowerStarConstantSheafEndOfOver_id {X Y : Scheme.{u}} (f : Y ⟶ X) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f (𝟙 Y) (Category.id_comp f) = 𝟙 _ :=
  -- the unit of `(𝟙 Y)^* ⊣ (𝟙 Y)_*` is identified with the identity by `upperStarId` and
  -- `lowerStarId`, and `lowerStarComp` with `𝟙 Y` is the identity
  sorry

/-- Pulling back sections is contravariant: the endomorphism attached to `g ≫ g'` is that of
`g'` followed by that of `g`. -/
lemma lowerStarConstantSheafEndOfOver_comp {X Y : Scheme.{u}} (f : Y ⟶ X) (g g' : Y ⟶ Y)
    (h : g ≫ f = f) (h' : g' ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f (g ≫ g') (by rw [Category.assoc, h', h]) =
      lowerStarConstantSheafEndOfOver f g' h' ≫ lowerStarConstantSheafEndOfOver f g h :=
  -- the unit of `(g ≫ g')^* ⊣ (g ≫ g')_*` is the composite of the units of `g` and `g'` under
  -- `upperStarComp` and `lowerStarComp`, and these satisfy the associativity coherences
  sorry

/-- A variant of `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_id` for an
endomorphism that is merely equal to the identity. -/
lemma lowerStarConstantSheafEndOfOver_of_eq_id {X Y : Scheme.{u}} (f : Y ⟶ X) (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) (h : g ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f g h = 𝟙 _ := by
  subst hg
  exact lowerStarConstantSheafEndOfOver_id f

/-- A variant of `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_comp` for an
endomorphism that is merely equal to a composite. -/
lemma lowerStarConstantSheafEndOfOver_of_eq_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (g g' g'' : Y ⟶ Y) (hg : g'' = g ≫ g') (h : g ≫ f = f) (h' : g' ≫ f = f)
    (h'' : g'' ≫ f = f) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f g'' h'' =
      lowerStarConstantSheafEndOfOver f g' h' ≫ lowerStarConstantSheafEndOfOver f g h := by
  subst hg
  exact lowerStarConstantSheafEndOfOver_comp f g g' h h'

end AlgebraicGeometry.Etale

end
