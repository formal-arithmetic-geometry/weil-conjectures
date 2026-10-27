module

public import Sheaf.RingTheory.FiniteCoefficientExpression
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Field.Defs

import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Filtration

/-!
# Base change of finite formal coefficient operators

Source: the agent coefficient-family argument in Steps 1--8 of
lem-trf-formal-coefficient-operator-base-change; Stacks Tags 0306 and 00IQ(2)
for Noetherianity and closedness of ideals. The intended application is the
coefficient transport in Bierstone--Milman 1997, Remark 9.11
(blueprint: lem-trf-formal-coefficient-operator-base-change).

The expressions and coefficient topology are concrete constructions, so none of
these statements assumes a lifted input or a surjective coefficient homomorphism.
-/

@[expose] public section

universe u v w z

namespace MvPowerSeries

/-- Evaluation is linear and has finite coefficient dependence, hence is continuous
for discrete coefficients. Source: coefficient-family argument, Steps 1--2
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: for multiplication use the finitely many decompositions of an output
multi-index. Insertion and extraction each select at most one input coefficient;
a matrix uses its finite row. Addition takes unions of these finite supports;
composition takes a finite union of the supports needed by the outer row.
Each primitive is linear, and addition and composition preserve linearity.
Fixing a finite row support fixes the output coordinate. Finite intersections of
these neighborhoods prove continuity in the discrete coefficient product topology. -/
theorem FiniteCoefficientExpression.linear_finite_continuous
    {R : Type u} [CommRing R] {n k m l : ℕ}
    (A : FiniteCoefficientExpression R n k m l) :
    (∀ H G, A.eval (H + G) = A.eval H + A.eval G) ∧
    (∀ (r : R) H, A.eval (r • H) = r • A.eval H) ∧
    (∀ (j : Fin l) (μ : Fin m →₀ ℕ),
      ∃ s : Finset (Fin k × (Fin n →₀ ℕ)),
        ∀ H G, (∀ a ∈ s, coeff a.2 (H a.1) = coeff a.2 (G a.1)) →
          coeff μ (A.eval H j) = coeff μ (A.eval G j)) ∧
    @Continuous _ _ (formalCoefficientTupleTopology R n k)
      (formalCoefficientTupleTopology R m l) A.eval := by
  sorry

/-- Coefficient transport intertwines evaluation, including on specified series.
Source: coefficient-family argument, Steps 1--3
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: induct on the finite expression. A ring homomorphism preserves the finite
convolution sums, the finite matrix sums, and the coefficient selected by an
insertion or partial extraction. Addition and composition follow inductively.
The transported syntax is itself a finite expression over the target ring, so
the linearity and continuity theorem applies to all of its inputs. -/
theorem FiniteCoefficientExpression.eval_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (σ : R →+* S)
    {n k m l : ℕ} (A : FiniteCoefficientExpression R n k m l)
    (H : Fin k → MvPowerSeries (Fin n) R) :
    (A.map σ).eval (fun j ↦ MvPowerSeries.map σ (H j)) =
      fun j ↦ MvPowerSeries.map σ (A.eval H j) := by
  sorry

/-- Equal operator expressions remain equal on unrestricted target inputs.
Source: coefficient-family argument, Step 3
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: evaluate the equality on a single monomial in a single tuple component.
This identifies every entry of their finite rows over the source ring. Apply the
coefficient homomorphism to those entries and use the finite row formula over
the target ring. No coefficient of the target input needs a source lift. -/
theorem FiniteCoefficientExpression.eval_eq_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (σ : R →+* S)
    {n k m l : ℕ} (A B : FiniteCoefficientExpression R n k m l)
    (h : A.eval = B.eval) : (A.map σ).eval = (B.map σ).eval := by
  sorry

/-- Equalities of values on specified inputs persist under coefficient transport.
Source: coefficient-family argument, Step 3
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: apply coefficient transport to the given equality, then rewrite both sides
by the intertwining identity of Step 2. The inputs may be different specified
series and the expressions may have different source variable sets. -/
theorem FiniteCoefficientExpression.value_eq_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (σ : R →+* S)
    {n k p h m l : ℕ} (A : FiniteCoefficientExpression R n k m l)
    (B : FiniteCoefficientExpression R p h m l)
    (H : Fin k → MvPowerSeries (Fin n) R) (G : Fin h → MvPowerSeries (Fin p) R)
    (e : A.eval H = B.eval G) :
    (A.map σ).eval (fun j ↦ MvPowerSeries.map σ (H j)) =
      (B.map σ).eval (fun j ↦ MvPowerSeries.map σ (G j)) := by
  sorry

/-- A specified inverse remains the inverse; transport does not choose a new one.
Source: coefficient-family argument, Step 3
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: apply the homomorphism to each finite entrywise inverse identity. It
preserves products, sums, zero and one, including for the empty matrix. -/
theorem formalCoefficientMatrix_inverse_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (σ : R →+* S)
    {k : ℕ} (M N : Matrix (Fin k) (Fin k) R)
    (h : M * N = 1 ∧ N * M = 1) :
    M.map σ * N.map σ = 1 ∧ N.map σ * M.map σ = 1 := by
  sorry

/-- A projection onto the common full-series kernel of any family of partial
coefficient tests stays such a projection after base change. Source:
coefficient-family argument, Step 4
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: let D be the union of the input coefficient indices selected by all tests,
including every complementary exponent. Image containment forces every row
indexed by D to be zero, by evaluating on monomials. Fixing the kernel forces
each column outside D to be the identity column. These entry identities survive
transport. The finite row formula then proves image containment and pointwise
fixing for arbitrary target series supported outside D. Infinite test families
and the empty family are both covered. -/
theorem FiniteCoefficientExpression.isKernelProjection_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (σ : R →+* S)
    {n : ℕ} (P : FiniteCoefficientExpression R n 1 n 1)
    {ι : Type z} (D : ι → FormalCoefficientTest n) (h : P.IsKernelProjection D) :
    (P.map σ).IsKernelProjection D := by
  sorry

/-- Ideal-valued corrections extend to all target series over a Noetherian
coefficient ring. Source: coefficient-family argument, Steps 5--7; Stacks 0306
and 00IQ(2) (blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: put B = S[[T]] and I = (T). Finite convolution shows that I^N consists of
series vanishing in total degrees below N. Geometric series invert 1-bh for
h in I, so I lies in the Jacobson radical. B is Noetherian by
lem-weil-pbc-power-series-noetherian. Apply
lem-weil-pbc-krull-intersection-jacobson to B/J, where J is the ideal generated
by the transported f's, to obtain intersection (J + I^N) = J. Thus J is closed
for coefficientwise convergence. The source correction on each monomial maps
into J by intertwining and preservation of convolution products. Finite target
linear combinations do also, so every polynomial truncation has correction in
J. Finite coefficient dependence gives convergence of their corrections for an
arbitrary target input, and closedness of J proves the claim. -/
theorem FiniteCoefficientExpression.hasIdealCorrection_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (σ : R →+* S) {n q : ℕ} (P : FiniteCoefficientExpression R n 1 n 1)
    (f : Fin q → MvPowerSeries (Fin n) R) (h : P.HasIdealCorrection f) :
    (P.map σ).HasIdealCorrection (fun j ↦ MvPowerSeries.map σ (f j)) := by
  sorry

/-- Coefficient regrouping is a ring identification of iterated and joint formal
series. Source: coefficient-family argument, Step 8
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: the equivalence between exponents on a disjoint union and pairs of
exponents gives inverse regrouping maps. Addition and one are coefficientwise.
For multiplication, both sides sum over exactly the same finite decompositions
of the pair of exponents. This makes no topological identification. -/
theorem flattenFormalCoefficients_ring_identification
    {R : Type u} [CommRing R] {x t : ℕ} :
    (∀ H : MvPowerSeries (Fin t) (MvPowerSeries (Fin x) R),
      unflattenFormalCoefficients (flattenFormalCoefficients H) = H) ∧
    (∀ H : MvPowerSeries (Fin x ⊕ Fin t) R,
      flattenFormalCoefficients (unflattenFormalCoefficients H) = H) ∧
    (∀ F G : MvPowerSeries (Fin t) (MvPowerSeries (Fin x) R),
      flattenFormalCoefficients (F + G) =
        flattenFormalCoefficients F + flattenFormalCoefficients G) ∧
    (∀ F G : MvPowerSeries (Fin t) (MvPowerSeries (Fin x) R),
      flattenFormalCoefficients (F * G) =
        flattenFormalCoefficients F * flattenFormalCoefficients G) ∧
    flattenFormalCoefficients (1 : MvPowerSeries (Fin t) (MvPowerSeries (Fin x) R)) = 1 := by
  sorry

/-- The formal coefficient target over any field is Noetherian, and the ideal
correction holds for every joint formal input. Source: coefficient-family
argument, Step 8; Stacks 0306
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: a field is Noetherian, and lem-weil-pbc-power-series-noetherian gives
Noetherianity of its finite-variable series ring. Apply the ideal-correction
base-change assertion to tau and to the unflattening of the arbitrary joint
input. Regrouping preserves subtraction and products and carries the generated
ideal into the ideal of the regrouped generators, giving the displayed result. -/
theorem FiniteCoefficientExpression.hasIdealCorrection_formalTarget
    {R : Type u} {L : Type v} [CommRing R] [Field L] {x t q : ℕ}
    (τ : R →+* MvPowerSeries (Fin x) L) (P : FiniteCoefficientExpression R t 1 t 1)
    (f : Fin q → MvPowerSeries (Fin t) R) (h : P.HasIdealCorrection f) :
    IsNoetherianRing (MvPowerSeries (Fin x) L) ∧
    ∀ H : MvPowerSeries (Fin x ⊕ Fin t) L,
      flattenFormalCoefficients ((P.map τ).scalarEval (unflattenFormalCoefficients H)) - H ∈
        Ideal.span (Set.range (fun j ↦ flattenFormalCoefficients (MvPowerSeries.map τ (f j)))) := by
  sorry

/-- All constructions respect identity and composition of coefficient maps,
including changes of coefficient variables that fix the operator variables.
Source: coefficient-family argument, Step 8
(blueprint: lem-trf-formal-coefficient-operator-base-change).

Proof: induct on the syntax. Each stored scalar is sent to rho(sigma(a)); each
stored full series has the same coefficientwise identity by map_map. The
insertion and extraction indices do not change. Finite sums and compositions
are preserved recursively. The identity map fixes every stored coefficient.
Specialize rho to any continuous change of the coefficient variables; since
these are coefficient homomorphisms, no operator variable is changed. -/
theorem FiniteCoefficientExpression.map_identity_comp
    {R : Type u} {S : Type v} {A : Type w} [CommRing R] [CommRing S] [CommRing A]
    (σ : R →+* S) (ρ : S →+* A) {n k m l : ℕ}
    (P : FiniteCoefficientExpression R n k m l) :
    P.map (RingHom.id R) = P ∧ (P.map σ).map ρ = P.map (ρ.comp σ) := by
  sorry

end MvPowerSeries
