/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Linear polynomial formal fibres as hypersurfaces

Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph.
(blueprint: lem-weil-pbc-polynomial-linear-formal-fibre-presentation)
-/

@[expose] public section

universe u

namespace Polynomial

/-- If the residue field of a polynomial prime above zero is a fraction field of the
coefficient domain, its completed fibre is a hypersurface with derivative one in the
coefficient generic fibre.
Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph.
(blueprint: lem-weil-pbc-polynomial-linear-formal-fibre-presentation)

Proof:
Let K be the fraction field of A. The canonical A-map to the residue field extends
uniquely to a K-isomorphism because both fields are fraction fields of A. Write f₀ for
the image of X under evaluation K[X] → κ(r) followed by this isomorphism. Its kernel
is (X - f₀): polynomial division by the monic linear polynomial gives the remainder
as evaluation at f₀. Localizing A[X]/r at the nonzero elements of A gives precisely
K[X]/(X - f₀). Tensoring this quotient with the completed polynomial local ring C
identifies r.Fiber C with (K ⊗[A] C)/(X - f₀). Replace K by the canonical zero-prime
residue field of A using uniqueness of fraction fields. In this ring let f be the
image of X minus the image of f₀. Extend d/dX from A[X] through localization at q,
completion, and localization at A minus zero using Tag 07PE. It annihilates A and
therefore K by the quotient rule, and sends the image of X to one. Thus D f = 1.
The quotient and tensor identifications give the asserted ring isomorphism. This
also applies when the fibre is zero: the same presentation has f a unit. -/
theorem linear_formalFiber_hypersurface
    (A : Type u) [CommRing A] [IsDomain A]
    (q : Ideal (Polynomial A)) [q.IsPrime]
    (r : Ideal (Polynomial A)) [r.IsPrime]
    [IsFractionRing A r.ResidueField]
    (hr : r ≠ ⊥) (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := (⊥ : Ideal A).Fiber C
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    letI : Algebra ℤ R := Ring.toIntAlgebra R
    ∃ (f : R) (D : Derivation ℤ R R), D f = 1 ∧
      Nonempty ((R ⧸ Ideal.span ({f} : Set R)) ≃+* r.Fiber C) := by sorry

end Polynomial
