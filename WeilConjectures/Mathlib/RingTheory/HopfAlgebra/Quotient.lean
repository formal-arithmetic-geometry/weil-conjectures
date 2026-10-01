/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Convolution products of algebra homomorphisms killing a Hopf ideal

If two algebra homomorphisms out of a Hopf algebra `A` vanish on a Hopf ideal `I`, then so does
their convolution product: both factor through the quotient Hopf algebra `A ⧸ I`, and the
quotient map is a bialgebra homomorphism.

## Blueprint

- `sk-d-geometry`: the points of a closed subgroup scheme `V(I)` of an affine group scheme form a
  subgroup.
-/

@[expose] public section

open WithConv

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Algebra R B]

namespace Ideal.IsHopfIdeal

/-- The convolution product of two algebra homomorphisms vanishing on a Hopf ideal vanishes on
it. (blueprint: `sk-d-geometry`) -/
theorem convMul_apply_eq_zero {I : Ideal A} [I.IsHopfIdeal R] {f g : A →ₐ[R] B}
    (hf : ∀ a ∈ I, f a = 0) (hg : ∀ a ∈ I, g a = 0) {a : A} (ha : a ∈ I) :
    (toConv f * toConv g) a = 0 := by
  let q : A →ₐc[R] A ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hf' : f = (Ideal.Quotient.liftₐ I f hf).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  have hg' : g = (Ideal.Quotient.liftₐ I g hg).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  rw [hf', hg', ← AlgHom.convMul_comp_bialgHom_distrib]
  have : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
  simp [this]

end Ideal.IsHopfIdeal
