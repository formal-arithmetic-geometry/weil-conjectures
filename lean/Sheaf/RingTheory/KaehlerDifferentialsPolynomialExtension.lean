/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Kähler differentials of a polynomial algebra over an algebra

Source: Stacks Project, Algebra, Tags 00RS, 00RV and 00RX
(blueprint: lem-weil-pbc-kahler-differentials-polynomial-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace KaehlerDifferential

/-- The canonical decomposition of the differentials of `A[z₁, …, zₑ]` over `R`, and
its finite free rank consequence. Source: Stacks Project, Algebra, Tags 00RS
(`lemma-exact-sequence-differentials`), 00RV (`lemma-differentials-base-change`), and
00RX (`lemma-differentials-polynomial-ring`)
(blueprint: lem-weil-pbc-kahler-differentials-polynomial-extension).

Proof:
1. The first exact sequence (lem-weil-pbc-kahler-differentials-first-exact-sequence)
   supplies `u : B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` and the surjection `v` to `Ω[B⁄A]`, with
   kernel equal to the image of `u`. Constants use def-weil-pbc-mv-polynomial-ring.
2. By lem-weil-pbc-polynomial-ring-kahler-basis, `Ω[B⁄A]` has basis `dzⱼ`.
   Thus the map `s : Bᵉ → Ω[B⁄R]` given by the sum of `bⱼ dzⱼ` makes `v ∘ s`
   an isomorphism.
3. Subtracting `s ((v ∘ s)⁻¹ (v ω))` shows `(x,b) ↦ u x + s b` is surjective.
   Applying `v` to an element of its kernel shows `b = 0`, reducing injectivity to `u`.
4. Set `P = R[z₁, …, zₑ]`. By lem-weil-pbc-polynomial-scalar-extension,
   `B = A ⊗[R] P`; lem-weil-pbc-kahler-differentials-base-change identifies
   `B ⊗[A] Ω[A⁄R]` with `Ω[B⁄P]`, sending `1 ⊗ dα` to `dα`.
5. The map `c : Ω[B⁄R] → Ω[B⁄P]` from the first exact sequence satisfies
   `c ∘ u = μ`, the isomorphism in step 4: both maps agree on the generators
   `1 ⊗ dα` (def-weil-pbc-kahler-differentials). Hence `u` is injective.
6. A basis of `Ω[A⁄R]` indexed by `Fin d` extends to a basis of its scalar extension.
   Combining it with the `e` variable differentials gives a basis indexed by `Fin (d+e)`.
-/
theorem exists_polynomial_extension_equiv
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (e : ℕ) :
    (∃ E : ((MvPolynomial (Fin e) A ⊗[A] KaehlerDifferential R A) ×
        (Fin e → MvPolynomial (Fin e) A)) ≃ₗ[MvPolynomial (Fin e) A]
          KaehlerDifferential R (MvPolynomial (Fin e) A),
      ∀ (x : MvPolynomial (Fin e) A ⊗[A] KaehlerDifferential R A)
        (b : Fin e → MvPolynomial (Fin e) A),
        E (x, b) = mapBaseChange R A (MvPolynomial (Fin e) A) x +
          ∑ j : Fin e, b j • D R (MvPolynomial (Fin e) A) (MvPolynomial.X j)) ∧
    (∀ d : ℕ, Nonempty (Module.Basis (Fin d) A (KaehlerDifferential R A)) →
      Nonempty (Module.Basis (Fin (d + e)) (MvPolynomial (Fin e) A)
        (KaehlerDifferential R (MvPolynomial (Fin e) A)))) := by
  sorry

end KaehlerDifferential
