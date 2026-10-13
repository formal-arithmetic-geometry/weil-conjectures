/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Coordinates from successive monic division

Source: Stacks Project, Algebra, proof of Tag 07BV and Tag 08JZ.
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- The triangular quotient has injective coordinates over k(x) compatible with evaluation.
Source: Stacks Project, Algebra, proof of Tag 07BV, successive monic division,
and Tag 08JZ, localization presentation
(blueprint: lem-weil-pbc-triangular-field-model-normal-form).

Proof: Put R = k[X] and D = R[1/h]. Algebraic independence embeds R into
F = k(x), and nonzero h lets this embedding extend to D. The presentation
R[T]/(hT-1) is D. Adjoining each new variable and quotienting by the lifted
monic p_i gives a free module with power basis of length e_i over the preceding
quotient. Basis.smulTower combines these to a D-basis indexed by the tuples of
exponents below e_i. Take the basis coordinate map and include every coefficient
of D into F. This is an injective k-linear map. Evaluation annihilates all
relations by hzero, so the expansion evaluates to the sum of the coordinate
coefficients times the products of b_i, using hyx, hyt and hyb. This proves the
compatibility formula for every polynomial. This theorem requires no independence
or algebraicity of b; those hypotheses belong to other steps. For m = 0 the
coordinate space has one coordinate and the quotient is D. A degree-zero monic
relation makes the quotient zero; hzero is then impossible in the field K, so
that case satisfies the theorem vacuously. -/
theorem triangularFieldModel_normal_form
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (hx : AlgebraicIndependent k x)
    (m : ℕ) (b : Fin m → K) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (y : Fin (d + 1 + m) → K) (e : Fin m → ℕ)
    (hh : h ≠ 0) (hp : ∀ i, (p i).Monic) (he : ∀ i, (p i).natDegree = e i)
    (hyx : ∀ j : Fin d, y ⟨j.val, by omega⟩ = x j)
    (hyt : y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹)
    (hyb : ∀ i : Fin m, y ⟨d + 1 + i.val, by omega⟩ = b i)
    (hzero : ∀ q ∈ triangularFieldModelEquations k d m h p,
      MvPolynomial.aeval y q = 0)
    : ∃ coord :
      (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)) →ₗ[k]
        (((i : Fin m) → Fin (e i)) → IntermediateField.adjoin k (Set.range x)),
      Function.Injective coord ∧
      ∀ q : MvPolynomial (Fin (d + 1 + m)) k,
        MvPolynomial.aeval y q =
          ∑ a : ((i : Fin m) → Fin (e i)),
            coord (Ideal.Quotient.mk _ q) a • (∏ i, b i ^ (a i).val) := by sorry

end FieldTheory
