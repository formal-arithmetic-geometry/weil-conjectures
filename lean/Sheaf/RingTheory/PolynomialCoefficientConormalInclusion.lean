/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # The conormal inclusion for polynomial coefficient reduction

Source: Stacks Project, Algebra, Tag 00S2, proof of lemma-exact-sequence-NL;
Smoothing Ring Maps, Tag 07CE, equation-sequence.
(blueprint: lem-weil-pbc-polynomial-coefficient-conormal-inclusion)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Coefficient expansion identifies the source of the conormal inclusion, its image,
and its injectivity criterion, without any projectivity assumption.
Source: Stacks Project, Algebra, Tag 00S2, proof of lemma-exact-sequence-NL;
Smoothing Ring Maps, Tag 07CE, equation-sequence.
(blueprint: lem-weil-pbc-polynomial-coefficient-conormal-inclusion)

Proof. Put Q = P[y], H = ker(Q → (P/I)[y]), J = ker φ, and A = P/I.
Compatibility gives H ≤ J. Coefficient expansion identifies the P-module H with
Q ⊗_P I: a polynomial in H has all coefficients in I, and its inverse sums the
monomial tensors of those coefficients. Reducing modulo HJ identifies H/HJ with
C ⊗_P I, because Q/J = C. Since I acts as zero on C, tensoring the quotient
I → I/I² identifies C ⊗_P I with C ⊗_A (I/I²). These identifications send
c ⊗ [x] to the class of a lift of c times the constant polynomial x.
Inclusion H ≤ J followed by J → J/J² kills HJ, hence descends to the required
C-linear map i. Its image is exactly the image of H in J/J², which is the stated
submodule equality after restriction to Q. Its kernel, under the identifications,
is (H ∩ J²)/HJ: the class of h vanishes in J/J² exactly when h lies in J².
Thus i is injective exactly when H ∩ J² = HJ. The representative formula is the
formula for the composite, and is independent of the chosen lifts since their
differences lie in J. The argument also applies to an empty variable set and to
I = P, when C and the tensor module are zero. -/
theorem polynomial_coefficient_conormal_inclusion
    (P : Type u) [CommRing P] (I : Ideal P) (m : ℕ)
    (C : Type v) [CommRing C] [Algebra (P ⧸ I) C]
    (α : MvPolynomial (Fin m) (P ⧸ I) →ₐ[P ⧸ I] C)
    (φ : MvPolynomial (Fin m) P →+* C)
    (hφeq : φ = α.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I)))
    (hφ : Function.Surjective φ) :
    ∃ (i : C ⊗[P ⧸ I] I.Cotangent →ₗ[C]
        (Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent),
      (∀ (c : C) (x : I) (y : (Extension.ofSurjective φ.toIntAlgHom hφ).ker),
        y.1 = MvPolynomial.C x.1 →
          i (c ⊗ₜ I.toCotangent x) = c • Extension.Cotangent.mk y) ∧
      i.range.restrictScalars (Extension.ofSurjective φ.toIntAlgHom hφ).Ring =
        (Submodule.comap (Extension.ofSurjective φ.toIntAlgHom hφ).ker.subtype
          (RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)))).map
            Extension.Cotangent.mk ∧
      (Function.Injective i ↔
        RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)) ⊓
            (RingHom.ker φ) ^ 2 =
          RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)) *
            RingHom.ker φ) := by sorry

end Algebra
