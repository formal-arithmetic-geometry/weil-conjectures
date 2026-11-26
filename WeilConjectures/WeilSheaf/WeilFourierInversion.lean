/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.WeilFourierTransform
import WeilConjectures.WeilSheaf.WeilFourierTransform
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Fourier inversion on constructible Weil complexes

This file states Fourier inversion for the Fourier transform on an affine space over a finite
field: the composite of the transforms for `ψ` and `ψ⁻¹` is the Tate twist by minus the rank, and
the square of the transform for `ψ` is negation pullback followed by that twist.

Both conclusions are isomorphisms of functors, so their components are Weil-equivariant
and natural in every constructible Weil complex. A finite coordinate type `n` represents
an affine space of arbitrary rank, including rank zero.

## Implementation details

For inversion, the composite is the transform of the convolution kernel with shift `2r`; that
kernel is the diagonal direct image of the constant sheaf with twist `-r` and shift `-2r`. The
diagonal is closed, hence proper, and the projection formula together with compact-support
composition and `pᵢ Δ = id` identify the result with the input twisted by `-r`.

For the square, the composite is the anti-diagonal kernel transform. With `a` the negation and
`γ = (id, a)` its graph, the projection formula identifies the transform with `a!` followed by
the twist; base change gives `a* a! ≅ id`, and `a² = id` gives `a* ≅ a!`.

## References

* Laumon, *Transformation de Fourier*, (1.2.2.1)--(1.2.2.3).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

/-- Negation on affine space is a morphism over the base. -/
instance AlgebraicGeometry.AffineSpace.isOver_neg (n : Type u) (S : AlgebraicGeometry.Scheme.{u}) :
    (AffineSpace.neg n S).IsOver S :=
  ⟨AffineSpace.neg_over n S⟩

namespace AlgebraicGeometry.WeilComplex

/-- Fourier inversion with the inverse additive character: `F_{ψ⁻¹} ∘ F_ψ` is the Tate twist by
`-r`, where `r` is the rank of the affine space, naturally in the Weil complex. -/
theorem nonempty_iso_affineFourierTransform_comp_inv
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ⁻¹ ≅
      tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))) :=
  by
  -- The proof in #1941 used `nonempty_affineFourierGeometry`,
  -- `nonempty_affineFourierKernelComposition`, `nonempty_affineFourierConvolutionKernelDelta`
  -- and `nonempty_affineFourierIdentityKernel`, none of which exists in the repository.
  sorry

/-- The same-character Fourier square is negation pullback followed by the rank Tate twist
`(-r)`, naturally in the Weil complex. -/
theorem nonempty_iso_affineFourierTransform_comp_self
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ ≅
      upperStar (l := l) (AffineSpace.neg n (Spec (CommRingCat.of k₀))) ⋙
        tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))) :=
  by
  -- The proof in #1941 used `nonempty_affineFourierGeometry`,
  -- `nonempty_affineFourierKernelSelfComposition`,
  -- `nonempty_affineFourierConvolutionKernelAntiDelta` and
  -- `nonempty_affineFourierAntiIdentityKernel`, none of which exists in the repository.
  sorry

end AlgebraicGeometry.WeilComplex
