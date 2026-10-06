/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Étale locality and composition of the base-change property

Two formal properties of the base-change property `BC(p, Λ, q)` of
`AlgebraicGeometry.Etale.BaseChangeProperty`, used in the smooth base change theorem to
reduce to smooth morphisms of relative dimension one:

- it is étale local on the source and on the target of `p`: if `X` is covered by étale
  `U_i ⟶ X` such that `U_i ⟶ S` factors as `f_i : U_i ⟶ V_i` followed by an étale
  `V_i ⟶ S`, and `BC(f_i, Λ, q)` holds for all `i`, then `BC(p, Λ, q)` holds;
- it is stable under composition: the base-change map of a composite square is the
  composite of the base-change maps of the two squares.

Isomorphisms satisfy the base-change property in every degree; with étale locality this
gives the base-change property for étale morphisms.

## Main statements

- `AlgebraicGeometry.Etale.BaseChangeProperty.of_etale_cover`: étale locality.
- `AlgebraicGeometry.Etale.BaseChangeProperty.comp`: stability under composition.
- `AlgebraicGeometry.Etale.baseChangeProperty_of_isIso`: isomorphisms satisfy `BC(p, Λ, q)`.

## References

- Stacks Project, Lemma 59.86.1, <https://stacks.math.columbia.edu/tag/0EZR>
- Stacks Project, Lemma 59.86.2, <https://stacks.math.columbia.edu/tag/0EZS>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Etale locality of the base-change property (degree `q`). This is a consequence of
blueprint `sbc-lem-etale-locality` (Stacks 0EZR), which is stated for a single Cartesian square
and a single sheaf.

Let `a_i : U_i ⟶ X` be a jointly surjective family of étale morphisms such that each composite
`U_i ⟶ X ⟶ S` factors as `f_i : U_i ⟶ V_i` followed by an étale morphism `b_i : V_i ⟶ S`. If
the base-change property `BC(f_i, Λ, q)` holds for every `i`, then `BC(p, Λ, q)` holds: the
restriction of the base-change map of a square on `p` to `U_i` is the base-change map of the
square on `f_i` obtained by base change along `V_i ⟶ S`, and a morphism of étale sheaves
which is an isomorphism on an étale covering is an isomorphism. -/
@[stacks 0EZR]
theorem Etale.BaseChangeProperty.of_etale_cover {q : ℤ} {ι : Type u} {U V : ι → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)] (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    (f : ∀ i, U i ⟶ V i) (b : ∀ i, V i ⟶ S) [∀ i, Etale (b i)] (w : ∀ i, f i ≫ b i = a i ≫ p)
    (hf : ∀ i, Etale.BaseChangeProperty Λ (f i) q) :
    Etale.BaseChangeProperty Λ p q :=
  sorry

/-- Base change for composites (degree `q`). This is a consequence of blueprint
`sbc-lem-base-change-composition` (Stacks 0EZS), which is stated for a single composite square
and a single sheaf.

If `BC(p₁, Λ, q)` and `BC(p₂, Λ, q)` hold, then so does `BC(p₁ ≫ p₂, Λ, q)`: a Cartesian square
on `p₁ ≫ p₂` along a quasi-compact quasi-separated `g` is the pasting of a Cartesian square on
`p₂` along `g` and a Cartesian square on `p₁` along the base change of `g`, which is again
quasi-compact quasi-separated, and the base-change map of the pasted square is the composite
of the base-change maps of the two squares. -/
@[stacks 0EZS]
theorem Etale.BaseChangeProperty.comp {Z : Scheme.{u}} {p₁ : X ⟶ Z} {p₂ : Z ⟶ S} {q : ℤ}
    (h₁ : Etale.BaseChangeProperty Λ p₁ q) (h₂ : Etale.BaseChangeProperty Λ p₂ q) :
    Etale.BaseChangeProperty Λ (p₁ ≫ p₂) q :=
  sorry

/-- An isomorphism `p` satisfies the base-change property `BC(p, Λ, q)` in every degree: for
a Cartesian square on an isomorphism, the base-change map is an isomorphism. This is the
elementary case where `p` is an isomorphism, so that `R^q p_*` is `p_*` (up to the pullback
isomorphism) in degree `0` and vanishes in the other degrees. -/
theorem Etale.baseChangeProperty_of_isIso (p : X ⟶ S) [IsIso p] (q : ℤ) :
    Etale.BaseChangeProperty Λ p q :=
  sorry

end AlgebraicGeometry
