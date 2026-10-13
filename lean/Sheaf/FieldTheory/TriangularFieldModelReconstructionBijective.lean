/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Reconstruction from bounded monomials in a triangular quotient

Source: Stacks Project, Algebra, proof of Tags 07BV and 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-reconstruction-bijective).
-/

@[expose] public section

universe u
namespace FieldTheory

/-- Reconstruction from localized coefficients and bounded monomials is bijective.
Source: Stacks Project, Algebra, proof of Tag 07BV and Tag 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-reconstruction-bijective).

Proof: The relation hT-1 identifies the quotient in the first d+1 variables
with D = k[X][1/h]. The coefficient homomorphism psi is uniquely determined by
its agreement with the base-ring map, by localization extensionality. Split off
one variable at a time. The universal property of the simultaneous quotient
identifies it with the successive quotients by the mapped p_i: in each direction,
send a variable to its corresponding quotient class. All defining relations vanish,
and the composites fix the coefficient ring and every variable, hence are identities.
Monicity survives these maps. The monic quotient power basis has exponents below e_i. Combine these
bases by Basis.smulTower and reindex the product by dependent exponent tuples.
More explicitly, monic division at the last variable gives a unique polynomial of
degree below e_i with coefficients in the preceding quotient. Induction expands
those coefficients uniquely in earlier bounded monomials. Thus every quotient
class has exactly one expansion indexed by the full bounded exponent tuple.
The basis synthesis map is exactly the displayed sum of psi(c a) times the
bounded monomials, hence is bijective. For m=0 use the singleton basis of D.
If some e_i=0, its monic polynomial is 1 and both the quotient and the function
space on the empty exponent set are zero. If h=0, the localization relation is
-1, so D and the quotient are zero as well. No field evaluation is used. -/
theorem triangularFieldModel_reconstruction_bijective
    (k : Type u) [Field k] (d m : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (e : Fin m → ℕ) (hp : ∀ i, (p i).Monic)
    (he : ∀ i, (p i).natDegree = e i)
    (psi : Localization.Away h →ₐ[k]
      (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)))
    (hpsi : ∀ r : MvPolynomial (Fin d) k,
      psi (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk _
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + m))) r)) :
    Function.Bijective
      (∑ a : ((i : Fin m) → Fin (e i)),
        (LinearMap.mulRight k (∏ i : Fin m,
          (Ideal.Quotient.mk _ (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val)).comp
            (psi.toLinearMap.comp (LinearMap.proj a)) :
        ((((i : Fin m) → Fin (e i)) → Localization.Away h) →ₗ[k]
          (MvPolynomial (Fin (d + 1 + m)) k ⧸
            Ideal.ofList (triangularFieldModelEquations k d m h p)))) := by
  sorry

end FieldTheory
