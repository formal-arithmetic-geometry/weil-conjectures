/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.LinearEquationLocalizationPolynomialCore
import WeilConjectures.RingTheory.LinearEquationLocalizationPolynomialFormula

/-!
# Localizing a polynomial algebra with one linear relation

For `B = A[x₁, …, x_r]/(∑ f_j x_j - 1)`, the localization `B_{f_i}` is a polynomial algebra over
`A_{f_i}` in the variables `x_j` with `j ≠ i`; in particular it is smooth.

## Implementation details

This fills in the computation omitted in Stacks. The inverse sends `x_i` to
`z = f_i⁻¹ (1 - ∑_{j ≠ i} f_j y_j)` and `x_j` to `y_j`; it kills the defining relation, and the
universal properties of polynomial rings, quotients and localizations show that both composites
are identities.

## References

* [Stacks, Tag 07EU]
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- For `B = A[x]/(∑ f_j x_j - 1)`, the localization `B_{f_i}` is the polynomial algebra over
`A_{f_i}` in the variables `x_j`, `j ≠ i`, with the eliminated variable sent to
`f_i⁻¹ (1 - ∑_{j ≠ i} f_j X_j)`.

The binder `i : Fin r` encodes the choice of one of the `r ≥ 1` variables.
The local algebra instance is the induced map on localizations, not extra data. -/
theorem linearEquationLocalizationPolynomial (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (i : Fin r) :
    let I : Ideal (MvPolynomial (Fin r) A) :=
      Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
    let B := MvPolynomial (Fin r) A ⧸ I
    let q := Ideal.Quotient.mk I
    let Af := Localization.Away (f i)
    let Bf := Localization.Away (algebraMap A B (f i))
    letI : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
    let x : Fin r → Bf := fun j ↦ algebraMap B Bf (q (X j))
    ∃ e : MvPolynomial {j : Fin r // j ≠ i} Af ≃ₐ[Af] Bf,
      e.toAlgHom = aeval (fun j ↦ x j.1) ∧
      (∀ j : {j : Fin r // j ≠ i}, e.symm (x j.1) = X j) ∧
      e.symm (x i) =
        C (IsLocalization.Away.invSelf (S := Af) (f i)) *
          (1 - ∑ j : {j : Fin r // j ≠ i},
            C (algebraMap A Af (f j.1)) * X j) := by
  dsimp
  obtain ⟨e, he, hf⟩ := linearEquationLocalizationPolynomialCore A r f i
  refine ⟨e, he, hf, ?_⟩
  exact linearEquationLocalizationPolynomialFormula A r f i e he hf

end MvPolynomial
