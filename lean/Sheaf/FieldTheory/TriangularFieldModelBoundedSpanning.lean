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

/-! # Bounded monomial spanning for triangular quotients

Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
-/

@[expose] public section

universe u
namespace FieldTheory

/-- Bounded monomials span the triangular quotient.
Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-bounded-spanning).

Proof: Identify the quotient by hT-1 with D=k[X][1/h] via the localization
presentation. Agreement on k[X] identifies psi with its canonical map. Split
off the last tower variable and identify the simultaneous quotient with the
successive monic quotients by the universal maps fixing every variable. Divide
an arbitrary representative by the mapped last monic polynomial. Its remainder
has degree below e_i, and represents the same quotient class. Inductively
expand each remainder coefficient in earlier bounded monomials. Collecting
coefficients gives the displayed expansion indexed by all bounded exponent
tuples. The base case m=0 is the localization presentation and its single
coefficient. If h=0 both rings are zero. If some e_i=0, monicity makes p_i=1,
so the quotient is zero; its zero element is represented by the unique function
on the empty exponent set. The argument needs no field evaluation. -/
theorem triangularFieldModel_bounded_spanning
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
    (q : (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p))) :
    ∃ c : (((i : Fin m) → Fin (e i)) → Localization.Away h), (∑ a : ((i : Fin m) → Fin (e i)),
        psi (c a) * (∏ i : Fin m,
          (Ideal.Quotient.mk _ (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val)) = q := by sorry

end FieldTheory
