/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# First-order coordinates for a smooth augmented algebra

Source: Stacks Project, Tag 05D5, the choice of basis lifts and the map Ψ₂.
(blueprint: lem-sbc-smooth-augmentation-first-order-coordinates)
-/

@[expose] public section

universe u

namespace Algebra

/-- Polynomial coordinates on the square-zero augmentation quotient.

Source: Stacks Project, Tag 05D5, proof through the assertion that Ψ₂ is an isomorphism.
(blueprint: lem-sbc-smooth-augmentation-first-order-coordinates)

Proof: Write I = ker ε. The split conormal sequence for B → C → B identifies I/I²
with Ω[C/B] tensored along ε with B. Smoothness makes this module finite projective.
Since B is local, it is free of finite rank n. Lift a basis to elements fᵢ of I and
let f be polynomial evaluation at these elements. Thus f sends the variables ideal
J into I. The augmentation splits C/I² as B ⊕ I/I², with square-zero second summand.
Likewise B[X]/J² is B ⊕ Bⁿ, with square-zero second summand. Evaluation is the identity
on B and the chosen basis map on the second summands, hence bijective. If n = 0,
both second summands vanish and evaluation on these quotients is the identity of B.
No finite generation of I itself or Noetherian hypothesis is used. -/
theorem exists_augmented_firstOrder_polynomial_coordinates
    (B C : Type u) [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C]
    [Smooth B C] (ε : C →ₐ[B] B) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) B →ₐ[B] C)
      (hf : MvPolynomial.idealOfVars (Fin n) B ≤
        (RingHom.ker ε.toRingHom).comap f.toRingHom),
      Function.Bijective (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2))) := by
  sorry

end Algebra
