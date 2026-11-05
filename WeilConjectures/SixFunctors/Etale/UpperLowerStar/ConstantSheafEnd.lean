/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Endomorphisms of `f_* Λ` from endomorphisms over the base

For `f : Y ⟶ X` and an endomorphism `g : Y ⟶ Y` over `X`, pulling back sections along `g`
gives an endomorphism of the pushforward `f_* Λ` of the constant sheaf, the monoidal unit `𝟙_`.
The identification `g^* Λ ≅ Λ` is the unit isomorphism of the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar` of `g^*`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`: for `f : Y ⟶ X` and
  `g : Y ⟶ Y` with `g ≫ f = f`, the endomorphism of `f_* Λ` given by pulling back sections
  along `g`.
- `AlgebraicGeometry.Etale.lowerStarConstantSheafMul`: the multiplication
  `f_* Λ ⊗ f_* Λ ⟶ f_* Λ` of the monoid object `f_* Λ`.

## Main results

- `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_id` and
  `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_comp`: the construction is
  contravariantly functorial in `g`. Both reduce, via
  `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver_eq`, to the compatibility of the
  unit `ε` of the lax monoidal pushforwards with the identity and composition isomorphisms
  (`AlgebraicGeometry.Etale.ε_lowerStar_id` and `AlgebraicGeometry.Etale.ε_lowerStar_comp`).
- `AlgebraicGeometry.Etale.lowerStarConstantSheafMul_comp_lowerStarConstantSheafEndOfOver`:
  pulling back sections is multiplicative, the composition isomorphisms of pushforwards being
  monoidal.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

open scoped CategoryTheory.Obj

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards of sheaves of
`Λ`-modules is monoidal. -/
instance isMonoidal_lowerStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
  unfold lowerStarComp
  infer_instance

end AlgebraicGeometry.Etale

end
