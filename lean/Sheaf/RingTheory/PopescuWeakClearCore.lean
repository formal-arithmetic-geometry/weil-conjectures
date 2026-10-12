module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Clearing equations and the inverse Jacobian

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the denominator-clearing paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-clear-core)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- Clear the defining equations and inverse-Jacobian certificate, retaining generation
of the localized kernel. No auxiliary relations are involved.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the denominator-clearing paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-clear-core)

Proof: Identify the polynomial ring over Rₚ with the localization of the polynomial
ring over R at the constant polynomials from R \ p. For each relation of P, multiply
by a common denominator of its finitely many coefficients, obtaining fⱼ over R.
The coefficient extension of fⱼ is a scalar unit times P.relation j. Consequently
these extensions generate exactly the kernel of evaluation, and fⱼ vanishes in D.
Partial differentiation commutes with coefficient extension and the scalar factors
have derivative zero, so the new Jacobian determinant is the old determinant times
the product of these units. Its evaluation in D is therefore a unit. Surjectivity
of the presentation evaluation lifts its inverse to a localized polynomial. The
product of that lift and the determinant differs from 1 by an element of the ideal
of the extended fⱼ. Express this membership as a finite linear combination. Clear
all coefficients in the inverse and in this combination with one denominator
outside p. The resulting polynomial identity holds after localization; multiply
by one further scalar outside p annihilating its error in the localization kernel.
This gives C s - h * det ∈ (f), with s outside p. The empty relation family uses
empty determinant and products equal to 1. -/
theorem exists_cleared_submersive_presentation_core
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {D : Type v} [CommRing D] [Algebra (Localization.AtPrime p) D]
    [Algebra R D] [IsScalarTower R (Localization.AtPrime p) D]
    (n m c : ℕ) (hc : c ≤ n + m)
    (P : SubmersivePresentation (Localization.AtPrime p) D (Fin (n + m)) (Fin c))
    (hmap : P.map = Fin.castLE hc) :
    ∃ (f : Fin c → MvPolynomial (Fin (n + m)) R)
      (s : R) (h : MvPolynomial (Fin (n + m)) R),
      s ∉ p ∧
      (MvPolynomial.C s - h * Matrix.det
        (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) ∈
          Ideal.span (Set.range f)) ∧
      (∀ j, aeval P.val (f j) = 0) ∧
      Ideal.map (MvPolynomial.map (algebraMap R (Localization.AtPrime p)))
        (Ideal.span (Set.range f)) = RingHom.ker (aeval P.val) := by sorry

end Algebra
