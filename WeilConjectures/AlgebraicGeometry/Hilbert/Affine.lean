/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!
# The Hilbert functor over an affine base

For `f : X ⟶ S` and an `S`-scheme `T` such that `T` and `X ×[S] T` are affine, a closed
subscheme of `X ×[S] T` is an ideal `I` of `Γ(X ×[S] T)`, and it is a point of `Hilb^d_{X/S}(T)`
if and only if `Γ(X ×[S] T) ⧸ I` is a finite, flat, finitely presented `Γ(T)`-algebra of rank
`d` at every prime.

## Main statements

- `AlgebraicGeometry.isHilbertSubscheme_iff_of_isAffine`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **The Hilbert condition over an affine base.** If `T` and `X ×[S] T` are affine, an ideal
sheaf `I` on `X ×[S] T` is a point of `Hilb^d_{X/S}(T)` if and only if the ring map
`Γ(T) ⟶ Γ(X ×[S] T) ⧸ I(⊤)` is finite, flat, of finite presentation and of rank `d` at every
prime. -/
theorem isHilbertSubscheme_iff_of_isAffine (f : X ⟶ S) (d : ℕ) (T : Over S) [IsAffine T.left]
    [IsAffine (pullback f T.hom)] (I : (pullback f T.hom).IdealSheafData) :
    IsHilbertSubscheme f d T I ↔
      ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).Finite ∧
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).Flat ∧
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).FinitePresentation ∧
        ∀ p, ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).finrank p = d :=
  sorry

end AlgebraicGeometry
