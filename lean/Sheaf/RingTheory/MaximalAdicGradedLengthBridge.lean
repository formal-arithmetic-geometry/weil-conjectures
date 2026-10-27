module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.NumberTheory.Bernoulli

/-! # Maximal-adic graded pieces and cumulative lengths

Source: Stacks Project, Algebra, Tags 00K8, 00IY, 00IV and 00JZ
(blueprint: lem-trf-maximal-adic-graded-length-bridge).

The subspaces in the conclusion are specified by their underlying sets: exactly
those of the canonical summand inclusions into the published associated graded ring.
This expresses its residue-field grading without choosing any coefficient field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace IsLocalRing

/-- The degree-zero algebra of the published associated graded ring, with the
residue-field type wrapper. This is exactly `Ideal.associatedGradedAlgebra`,
whose coefficient type is written as the literal quotient `R/m`.
Source: Stacks Project, Algebra, Tag 00K8
(blueprint: lem-trf-maximal-adic-graded-length-bridge). -/
noncomputable instance maximalAdicResidueAlgebra (R : Type u) [CommRing R] [IsLocalRing R] :
    Algebra (ResidueField R) (Ideal.associatedGraded (maximalIdeal R)) :=
  Ideal.associatedGradedAlgebra (maximalIdeal R)

/-- The maximal-adic algebra is standard graded; quotient lengths are cumulative
homogeneous dimensions, and an eventual polynomial for the latter integrates to
an eventual nonzero polynomial of positive leading coefficient for the former.
Source: Stacks Project, Algebra, Tags 00K8, 00IY, 00IV and 00JZ
(blueprint: lem-trf-maximal-adic-graded-length-bridge).

Proof plan:
1. Noetherianity gives finitely many generators of the maximal ideal, including
   the empty list when it is zero. Induction on i shows that degree-i monomials
   generate its ith power. Modulo the next power, coefficients descend to R/m.
   The associated-graded ring laws identify the products with these classes.
   Thus monomials span each summand, each is finite dimensional, and the
   degree-one classes generate the whole direct sum. This is precisely
   GradedAlgebra.IsStandard (def-pc-standard-graded-algebra).
2. The maximal ideal kills each summand. Its R-submodules are therefore exactly
   its residue-field subspaces. A basis flag and strict dimension growth show
   that its composition length equals its dimension (Tag 00IY).
3. The canonical short exact sequence with terms m^i/m^(i+1), R/m^(i+1), R/m^i
   and Module.length_eq_add_of_exact give the cumulative formula by induction,
   starting with R/m^0 = 0. The zeroth summand is the nonzero residue field,
   of dimension one, giving positivity for n at least one.
4. If the dimensions eventually equal P, expand P in powers and use the rational
   power-sum polynomials from lem-trf-rational-power-sum-formula (sum_range_pow).
   Their linear combination A has A(n)-A(a) equal to the sum of P(i) from a to
   n-1. Set Q(X)=A(X)+H_R(a)-A(a). Then Q(n)=H_R(n) for n at least a.
   This includes P=0 and is the discrete summation in Tag 00JZ.
5. Since H_R(n) is at least one, Q is nonzero. A negative leading coefficient
   would make Q(n) negative for all sufficiently large positive n, by bounding
   the lower terms by C*n^(degree-1). A constant Q is itself positive. Hence
   its leading coefficient is strictly positive. Take N at least one and a.
-/
theorem maximalAdicGradedLengthBridge (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    ∃ 𝒜 : ℕ → Submodule (ResidueField R) (Ideal.associatedGraded (maximalIdeal R)),
      (∀ i : ℕ, (𝒜 i : Set (Ideal.associatedGraded (maximalIdeal R))) =
        Set.range (DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal R)) i)) ∧
      ∃ (_grading : GradedAlgebra 𝒜),
        GradedAlgebra.IsStandard (k := ResidueField R) 𝒜 ∧
        (∀ (t : ℕ) (y : Fin t → ↥(maximalIdeal R ^ 1)),
          Ideal.span (Set.range (fun j : Fin t ↦ (y j).val)) = maximalIdeal R →
          Algebra.adjoin (ResidueField R)
            (Set.range (fun j : Fin t ↦
              DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal R)) 1
                (Submodule.Quotient.mk (y j)))) = ⊤ ∧
          ∀ i : ℕ, Submodule.span (ResidueField R)
            (Set.range (fun f : Fin i → Fin t ↦
              ∏ j : Fin i,
                DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal R)) 1
                  (Submodule.Quotient.mk (y (f j))))) = 𝒜 i) ∧
        (∀ i : ℕ, Module.Finite (ResidueField R) (𝒜 i) ∧
          Module.length R (Ideal.associatedGradedPiece (maximalIdeal R) i) =
            (Module.finrank (ResidueField R) (𝒜 i) : ℕ∞)) ∧
        (∀ n : ℕ, 1 ≤ n →
          IsFiniteLength R (R ⧸ maximalIdeal R ^ n) ∧
          Module.length R (R ⧸ maximalIdeal R ^ n) =
            ((∑ i ∈ Finset.range n, Module.finrank (ResidueField R) (𝒜 i)) : ℕ∞) ∧
          1 ≤ Module.length R (R ⧸ maximalIdeal R ^ n)) ∧
        (∀ P : Polynomial ℚ,
          (∃ a : ℕ, ∀ i : ℕ, a ≤ i →
            (Module.finrank (ResidueField R) (𝒜 i) : ℚ) = P.eval (i : ℚ)) →
          ∃ Q : Polynomial ℚ, Q ≠ 0 ∧ 0 < Q.leadingCoeff ∧
            ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
              ((Module.length R (R ⧸ maximalIdeal R ^ n)).toNat : ℚ) =
                Q.eval (n : ℚ)) := by
  sorry

end IsLocalRing
