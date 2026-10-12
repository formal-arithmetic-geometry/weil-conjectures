/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.RingTheory.StrictlyStandardElement
public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Desingularization with an annihilator bound

Source: Stacks Project, Tag 07CT, first paragraph of the proof, applying Tag 07CR.
(blueprint: lem-weil-pbc-desingularize-annihilator-construction).
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Construct a factorization with the relative annihilator bound, before any comparison
with the singular ideal of `D` over `R`. No annihilator equality in `R` is needed here.

Source: Stacks Project, Tag 07CT, first paragraph of the proof, applying Tag 07CR.

Proof: `D` is Noetherian since it is finitely presented over the Noetherian ring `R`.
Base change `A` to `D ⊗[R] A`, which is finitely presented over `D`. Give `Λ` its
`D`-algebra structure induced by `δ`. The tensor map sends `d ⊗ a` to `δ d * α a`.
Strict standardness is preserved by base change (Tag 07CC). The quotient map in `hquot`
induces the `D`-algebra section sending the class of `d ⊗ a` to `d` times the image of
`a` in `D/π⁴D`. On pure tensors its composite with the map to `Λ/π⁴Λ` agrees with the
tensor map by `hquot`; additive generation by pure tensors gives agreement everywhere.
Apply desingularization (Tag 07CR) over `D`. Retain its finite presentation over `D` and
its bound by the annihilator of `Ann_D(π²)/Ann_D(π)`. An element `r` is in that annihilator
exactly when `π_D² * x = 0` implies `r * π_D * x = 0` for every `x`. Restrict the tensor
factorization to the two factors and restrict the scalars of the map to `Λ` to `R`.
The structure map `dB` supplies the indicated `D`-algebra structure on `B`.
(blueprint: lem-weil-pbc-desingularize-annihilator-construction). -/
theorem exists_desingularization_annihilator_bound
    (R : Type u) (Λ : Type v) (A : Type w) (D : Type z)
    [CommRing R] [CommRing Λ] [CommRing A] [CommRing D]
    [Algebra R Λ] [Algebra R A] [Algebra R D] [IsNoetherianRing R]
    [FinitePresentation R A] [FinitePresentation R D]
    (π : R) (α : A →ₐ[R] Λ) (δ : D →ₐ[R] Λ)
    (hΛ : ∀ l : Λ, l * algebraMap R Λ π = 0 ↔
      l * (algebraMap R Λ π) ^ 2 = 0)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hquot : ∃ φ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
      ∀ (a : A) (d : D),
        φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d)) :
    ∃ (B : Type (max u v w z)) (_ : CommRing B) (_ : Algebra R B),
      ∃ (β : B →ₐ[R] Λ) (aB : A →ₐ[R] B) (dB : D →ₐ[R] B),
        @FinitePresentation D B _ _ dB.toRingHom.toAlgebra ∧
        β.comp aB = α ∧ β.comp dB = δ ∧
        Ideal.span (dB ''
          {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
            r * algebraMap R D π * x = 0}) ≤
          @singularIdeal D B _ _ dB.toRingHom.toAlgebra := by
  sorry

end Algebra
