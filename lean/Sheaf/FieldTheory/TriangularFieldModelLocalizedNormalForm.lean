/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra

/-! # Unique localized coefficients for a triangular monic quotient -/

@[expose] public section

universe u v

namespace FieldTheory

/-- Successive monic division gives unique coefficients in the explicit localization.
Source: Stacks Project, Algebra, proof of Tag 07BV (the triangular monic quotient
before embedding it in the generated field), and Tag 08JZ (localization presentation).
(blueprint: lem-weil-pbc-triangular-field-model-localized-normal-form).

Proof: Set R = k[X] and D = R[1/h]. Identify the quotient by hT-1 with D
using the localization presentation. At stage i, regard the polynomial ring on
its first d+1+i variables modulo the preceding equations as the coefficient ring;
adjoining the next variable and quotienting by p_i is AdjoinRoot of the mapped
polynomial. Mapping preserves monicity. If e_i is positive, the leading
coefficient stays one and its degree stays e_i. The power basis of this monic
quotient has exponents below e_i. Inductively multiply these bases with the
previous D-basis and reindex the product by dependent exponent tuples. The
base case m=0 is D with its one-element basis. Splitting off the last variable
and the quotient universal property identify this iterated quotient with the
simultaneous ideal-of-list quotient. Restrict the D-linear coordinate equivalence
to k and identify finitely supported functions with functions on the finite
exponent set. This gives nf. Evaluation at y factors through the simultaneous
quotient by hzero. Its restriction to D is phi: the maps agree on R by hphi,
and the localization universal property determines the inverse of h. The
identifications hyx, hyt and hyb therefore evaluate each power-basis monomial
to the corresponding product of powers of b_i. Applying this evaluation map
to the finite basis expansion proves the formula. If some e_i=0, monicity
makes p_i=1; hzero would give 1=0 in K, so eliminate this impossible case.
No algebraic independence is needed. In particular this is a basis over D,
not a finite basis over k. -/
theorem triangularFieldModel_localized_normal_form
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (m : ℕ) (b : Fin m → K)
    (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (y : Fin (d + 1 + m) → K) (e : Fin m → ℕ)
    (hp : ∀ i, (p i).Monic) (he : ∀ i, (p i).natDegree = e i)
    (hyx : ∀ j : Fin d, y ⟨j.val, by omega⟩ = x j)
    (hyt : y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹)
    (hyb : ∀ i : Fin m, y ⟨d + 1 + i.val, by omega⟩ = b i)
    (hzero : ∀ q ∈ triangularFieldModelEquations k d m h p,
      MvPolynomial.aeval y q = 0)
    (phi : Localization.Away h →ₐ[k] K)
    (hphi : ∀ r : MvPolynomial (Fin d) k,
      phi (algebraMap _ (Localization.Away h) r) = MvPolynomial.aeval x r) :
    ∃ nf : (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)) ≃ₗ[k]
        (((i : Fin m) → Fin (e i)) → Localization.Away h),
      ∀ q : MvPolynomial (Fin (d + 1 + m)) k,
        MvPolynomial.aeval y q =
          ∑ a : ((i : Fin m) → Fin (e i)),
            phi (nf (Ideal.Quotient.mk _ q) a) * (∏ i, b i ^ (a i).val) := by
  sorry

end FieldTheory
