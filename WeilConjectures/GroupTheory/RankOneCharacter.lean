/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Rank-one characters of a split cyclic extension

Let `P` be a group equipped with an automorphism `α`, and let `W = P ⋊_α ℤ` be the associated
split cyclic extension, with multiplication `(u, n) * (v, m) = (u * α ^ n v, n + m)`. We realise
`W` as Mathlib's `SemidirectProduct`, namely `N ⋊[φ] Multiplicative ℤ` for a homomorphism
`φ : Multiplicative ℤ →* MulAut N`. Under this identification the degree map `deg` is
`SemidirectProduct.rightHom`, the subgroup `P` is `SemidirectProduct.rightHom.ker`, which by
`SemidirectProduct.range_inl_eq_ker_rightHom` is the range of `SemidirectProduct.inl`, and the
chosen degree-one element `γ = (1, 1)` is `SemidirectProduct.inr (Multiplicative.ofAdd 1)`.

A rank-one character is a homomorphism `χ : W → Eˣ` for a field `E`; it has finite geometric
image when its restriction to `P` has finite image. Such a character splits as the product of an
unramified part `χ_z : w ↦ z ^ deg w`, where `z = χ γ`, and a finite part
`χ_fin : w ↦ χ w * z ^ (-deg w)`.

## Main declarations

* `SemidirectProduct.gamma`: the chosen degree-one element `γ = (1, 1)` of
  `N ⋊[φ] Multiplicative ℤ`.
* `SemidirectProduct.degreeCharacter`: the character `χ_z : w ↦ z ^ deg w` attached to a unit `z`.
* `SemidirectProduct.finitePart`: the finite part `χ_fin = χ / χ_z` of a rank-one character `χ`,
  where `z = χ γ`.
* `SemidirectProduct.rankOne_factorization`: a rank-one character with finite geometric image
  factors as `χ = χ_fin * χ_z`, the finite part is trivial on `γ`, and its image is exactly the
  geometric image `χ (P)` of `χ`.
-/

@[expose] public section

namespace SemidirectProduct

variable {N : Type*} [Group N] {E : Type*} [Field E]

/-- Blueprint `sk-d-ab-rankone`: A split cyclic extension and rank-one characters. The chosen
degree-one element `γ = (1, 1)` of the split cyclic extension `N ⋊[φ] Multiplicative ℤ`; every
element of the extension is uniquely of the form `u * γ ^ n` with `u` in the copy of `N`. -/
abbrev gamma (φ : Multiplicative ℤ →* MulAut N) : N ⋊[φ] Multiplicative ℤ :=
  inr (Multiplicative.ofAdd 1)

/-- Blueprint `sk-d-ab-rankone`: A split cyclic extension and rank-one characters. The rank-one
character `χ_z` sending an element `w` of the split cyclic extension to `z ^ deg w`, where the
degree `deg w` is read off by `SemidirectProduct.rightHom`. -/
def degreeCharacter (φ : Multiplicative ℤ →* MulAut N) (z : Eˣ) :
    (N ⋊[φ] Multiplicative ℤ) →* Eˣ :=
  (zpowersHom Eˣ z).comp rightHom

/-- Blueprint `sk-d-ab-rankone`: A split cyclic extension and rank-one characters. The finite
part `χ_fin` of a rank-one character `χ`, obtained by dividing `χ` by the character `χ_z`
attached to the unit `z = χ γ`; explicitly `χ_fin w = χ w * z ^ (-deg w)`. -/
def finitePart {φ : Multiplicative ℤ →* MulAut N} (χ : (N ⋊[φ] Multiplicative ℤ) →* Eˣ) :
    (N ⋊[φ] Multiplicative ℤ) →* Eˣ :=
  χ / degreeCharacter φ (χ (gamma φ))

/-- Blueprint `sk-p-rankone`: Rank-one factorization. A rank-one character `χ` with finite
geometric image factors as the product of its finite part and the degree character attached to
`z = χ γ`, the finite part is trivial on `γ`, and the image of the finite part is exactly the
geometric image `χ (P)`; combined with the hypothesis `hχ` this last equality shows that the
finite part has finite image. -/
theorem rankOne_factorization {φ : Multiplicative ℤ →* MulAut N}
    (χ : (N ⋊[φ] Multiplicative ℤ) →* Eˣ)
    (hχ : (Set.range (χ.comp (inl : N →* _))).Finite) :
    χ = finitePart χ * degreeCharacter φ (χ (gamma φ)) ∧
      finitePart χ (gamma φ) = 1 ∧
      Set.range (finitePart χ) = Set.range (χ.comp (inl : N →* _)) := by
  sorry

end SemidirectProduct
