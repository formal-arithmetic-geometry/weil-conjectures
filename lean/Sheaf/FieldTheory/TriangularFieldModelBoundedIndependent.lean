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

/-! # Bounded monomial independent for triangular quotients

Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
-/

@[expose] public section

universe u
namespace FieldTheory

/-- Bounded monomials have no nonzero vanishing expansion.
Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-bounded-independent).

Proof: First identify the quotient of the first d+1 variables by hT-1 with
D=k[X][1/h], using the localization presentation. Agreement on k[X] determines
psi uniquely, including the inverse of h. Split off the last tower variable,
and identify the simultaneous quotient with the quotient of the previous
stage's polynomial ring by the mapped last monic relation. The universal maps
send each variable to its class; their composites fix every variable and the
coefficient ring. Over a nonzero previous stage, mapping preserves the leading
coefficient one and degree e_i. Uniqueness of remainder upon division by this
monic polynomial says all coefficients of a vanishing bounded expansion in
the last variable vanish. Induction applies the same assertion to their bounded
expansions in earlier variables, giving c(a)=0 for every tuple a. For m=0 this
is injectivity of the localization identification. If h=0 the coefficient ring
is zero. If an e_i=0 the exponent set is empty and every coefficient function
is zero; hence the assertion remains true. No field evaluation is used. -/
theorem triangularFieldModel_bounded_independent
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
          (⟨j.val, by omega⟩ : Fin (d + 1 + m))) r))
    (c : (((i : Fin m) → Fin (e i)) → Localization.Away h))
    (hc : (∑ a : ((i : Fin m) → Fin (e i)),
        psi (c a) * (∏ i : Fin m,
          (Ideal.Quotient.mk _ (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val)) = 0) : c = 0 := by sorry

end FieldTheory
