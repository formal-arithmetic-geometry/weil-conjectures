/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.WeilFourierTransform
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import Sheaf.Paper.FieldTorAmplitude
import Sheaf.Paper.FourierKernelConvolution

/-!
# Fourier inversion on constructible Weil complexes

Source: blueprint main-20261015, `sec-fourier-transform/sk-thm-inversion/lem-fd-inversion.md`
and its proof (blueprint: lem-fd-inversion); Laumon, Transformation de Fourier,
(1.2.2.1)--(1.2.2.3).

Both conclusions are isomorphisms of functors, so their components are Weil-equivariant
and natural in every constructible Weil complex. A finite coordinate type `n` represents
an affine space of arbitrary rank, including rank zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

/-- Fourier inversion with the inverse additive character, functorially in the Weil complex.
Source: blueprint main-20261015, `sk-thm-inversion/lem-fd-inversion.md`, first formula;
Laumon, Transformation de Fourier, (1.2.2.1)--(1.2.2.3) (blueprint: lem-fd-inversion).

Proof: `lem-fd-kernel-composition` writes the composite as the transform of the convolution
kernel with shift `2r`. By `lem-fd-convolution-kernel`, that kernel is the diagonal direct
image of the constant sheaf with twist `-r` and shift `-2r`. The diagonal is closed, hence
proper. Its projection formula from `prop-functor-package`, with the finite Tor amplitude
provided by `lem-weil-field-tor-amplitude`, identifies the integrand with the diagonal direct
image of the input. Compact-support composition and both identities `pᵢ Δ = id` identify
its pushforward with the input. The two shifts cancel, leaving its Tate twist `-r`.
Every comparison is natural and Weil-equivariant. -/
theorem nonempty_iso_affineFourierTransform_comp_inv
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ⁻¹ ≅
      tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))) :=
  sorry

/-- The same-character Fourier square is negation pullback followed by the rank Tate twist.
Source: blueprint main-20261015, `sk-thm-inversion/lem-fd-inversion.md`, second formula;
Laumon, Transformation de Fourier, (1.2.2.1)--(1.2.2.3) (blueprint: lem-fd-inversion).

Proof: `lem-fd-kernel-composition` and the second formula of `lem-fd-convolution-kernel`
identify the composite with the anti-diagonal kernel transform, with twist `-r` and shifts
`-2r` and `2r`. Write `a` for negation and `γ = (id,a)` for its graph. The graph is closed
and proper. The projection formula of `prop-functor-package`, using
`lem-weil-field-tor-amplitude`, and compact-support composition identify this transform with
`a!` followed by the Tate twist, after cancelling shifts. Base change in the square with
both maps to the bottom right equal to `a` and the other maps identities gives `a* a! ≅ id`.
Composition and `a² = id` give `a! a! ≅ id`, hence `a* ≅ a!`. The twist comes from the point
and commutes with this pullback by projection formula. All comparisons are natural and
Weil-equivariant. -/
theorem nonempty_iso_affineFourierTransform_comp_self
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ ≅
      upperStar (l := l) (AffineSpace.neg n (Spec (CommRingCat.of k₀))) ⋙
        tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))) :=
  sorry

end AlgebraicGeometry.WeilComplex
