module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
universe u
namespace MvPolynomial
/-- Core existence and inverse-on-free-variables part of the localization computation.

The source is Stacks Project, Tag 07EU, `lemma-final-solve`, where the
calculation is omitted. Construct the forward map by the polynomial universal
property, sending each free variable to the corresponding class in the
localization. For the inverse, put
`z = fᵢ⁻¹ (1 - ∑ j ≠ i, fⱼ yⱼ)`, evaluate the original polynomial ring by
sending `xᵢ` to `z` and the other variables to `yⱼ`, and factor through the
linear relation because `fᵢ z + ∑ j ≠ i fⱼ yⱼ - 1 = 0`. The image of `fᵢ`
is a unit, so the localization universal property extends this map to `Bf`.
The inverse followed by the forward map fixes each free polynomial variable.
The forward followed by the inverse fixes the classes of the other variables,
and fixes `xᵢ` because the relation gives
`1 - ∑ j ≠ i, fⱼ xⱼ = fᵢ xᵢ`, so multiplying by `fᵢ⁻¹` recovers `xᵢ`.
Polynomial uniqueness, quotient surjectivity and localization uniqueness now
show both composites are identities. The inverse therefore sends every free
class to its variable, as claimed.
(blueprint: lem-weil-pbc-linear-equation-localization-polynomial-core) -/
theorem linearEquationLocalizationPolynomialCore (A : Type u) [CommRing A]
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
      (∀ j : {j : Fin r // j ≠ i}, e.symm (x j.1) = X j) := by
  sorry
end MvPolynomial
