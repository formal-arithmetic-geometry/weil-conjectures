module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Adjoin.Tower

/-!
# Finite maps of strict affinoids and canonical reduction

Source: BGR, Non-Archimedean Analysis, Theorem 6.3.5/1; Temkin,
A new proof of the Gerritzen--Grauert theorem, introduction and section 2
(blueprint: lem-trf-finite-affinoid-canonical-reduction).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- A finite algebra map of nonzero reduced strict affinoids is continuous, contracts
character suprema, and induces a finite map on canonical reductions over the residue
field. The existentially specified functions, subrings, ideals, and maps are fixed by
exact formulas: `ρA`, `ρB` are character suprema, `A₀`, `B₀` are their closed unit balls,
`IA`, `IB` their open unit ideals, and `V ⧸ m` is the residue scalar ring. The three
quotient maps are specified on every representative. Thus `f.comp sA = sB` expresses
linearity over the residue field without choosing algebra instances on the quotients.

Source: BGR Theorem 6.3.5/1 and Temkin, A new proof of the Gerritzen--Grauert theorem,
introduction, printed p. 2, and section 2
(blueprint: lem-trf-finite-affinoid-canonical-reduction).

Proof plan from the DAG:
1. By `lem-trf-affinoid-supremum-seminorm-calculus`, maximal residue fields are finite
   over K, hence equal K by algebraic closedness. The quotient norm bound makes the
   residue characters continuous, identifying the maximal-ideal and character suprema.
2. Arbitrary-homomorphism contraction in that lemma gives the spectral inequality.
   `lem-trf-affinoid-spectral-banach-norm` bounds the quotient norm on B by a constant
   times its spectral norm; combined with the quotient bound on A this proves continuity.
3. Ultrametric and submultiplicative spectral inequalities give the closed unit subrings
   and open unit ideals. Scalar norms give V and m and the two residue scalar maps.
   Contraction induces `[a] ↦ [φ(a)]`, and scalar compatibility gives the displayed square.
4. `lem-trf-finite-affinoid-spectral-equation` gives monic equations with unit-ball
   coefficients for unit-ball elements. Reducing them proves integrality on reductions.
   The construction also works for nonreduced algebraic Tate quotients using maximal
   residue norms; maximal ideals exist by `lem-weil-pbc-proper-ideal-contained-in-maximal`.
5. For an affinoid domain use `lem-trf-tate-normalization-lift` and
   `lem-trf-tate-spectral-generic-reduction-rank`: the reduction is reduced, torsion-free
   and generically finite over the residue polynomial ring. Step 4 gives integrality;
   `lem-trf-integral-generic-finite-algebra` gives module finiteness and thus finite type.
6. `lem-trf-tate-submodule-norm-controlled-generators` makes the Tate algebra Noetherian,
   hence also its quotients. Use `lem-weil-pbc-noetherian-finitely-many-minimal-primes`
   and `lem-weil-pbc-prime-contains-minimal-prime` to pass to finitely many domain
   quotients. Their spectral norms have maximum equal to the original norm, so the
   original reduction embeds in the product of their reductions.
7. By step 4 the product is integral over the original reduction, and by step 5 it is
   finite type over the residue field. `lem-sc-finite-generated-integral-subring` makes
   the product module finite; `lem-sfb-artin-tate-subalgebra-finite-type` makes the
   original reduction finite type over the residue field.
8. Apply step 7 to B. Its finite residue-algebra generators also generate over the
   reduction of A; step 4 makes them integral. Apply
   `lem-sc-finite-generated-integral-subring` to conclude `f.Finite`.
-/
theorem finite_canonicalReduction
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K]
    (A : Type v) [NormedCommRing A] [Algebra K A] [Nontrivial A] [IsReduced A]
    (B : Type w) [NormedCommRing B] [Algebra K B] [Nontrivial B] [IsReduced B]
    (hA : IsAffinoidQuotient K A (algebraMap K A))
    (hB : IsAffinoidQuotient K B (algebraMap K B))
    (φ : A →ₐ[K] B) (hφ : φ.Finite) :
    Continuous φ ∧
      ∃ (ρA : A → ℝ) (ρB : B → ℝ),
        (∀ a : A, ρA a = sSup {r : ℝ | ∃ χ : A →ₐ[K] K, Continuous χ ∧ r = ‖χ a‖}) ∧
        (∀ b : B, ρB b = sSup {r : ℝ | ∃ χ : B →ₐ[K] K, Continuous χ ∧ r = ‖χ b‖}) ∧
        (∀ a : A, ρB (φ a) ≤ ρA a) ∧
        ∃ (A₀ : Subring A) (B₀ : Subring B) (IA : Ideal A₀) (IB : Ideal B₀)
          (V : Subring K) (m : Ideal V),
          (∀ a : A, a ∈ A₀ ↔ ρA a ≤ 1) ∧
          (∀ b : B, b ∈ B₀ ↔ ρB b ≤ 1) ∧
          (∀ a : A₀, a ∈ IA ↔ ρA a.val < 1) ∧
          (∀ b : B₀, b ∈ IB ↔ ρB b.val < 1) ∧
          (∀ c : K, c ∈ V ↔ ‖c‖ ≤ 1) ∧
          (∀ c : V, c ∈ m ↔ ‖c.val‖ < 1) ∧
          ∃ (sA : V ⧸ m →+* A₀ ⧸ IA) (sB : V ⧸ m →+* B₀ ⧸ IB)
            (f : A₀ ⧸ IA →+* B₀ ⧸ IB),
            (∀ c : V, ∃ a : A₀, a.val = algebraMap K A c.val ∧
              sA (Ideal.Quotient.mk m c) = Ideal.Quotient.mk IA a) ∧
            (∀ c : V, ∃ b : B₀, b.val = algebraMap K B c.val ∧
              sB (Ideal.Quotient.mk m c) = Ideal.Quotient.mk IB b) ∧
            (∀ a : A₀, ∃ b : B₀, b.val = φ a.val ∧
              f (Ideal.Quotient.mk IA a) = Ideal.Quotient.mk IB b) ∧
            f.comp sA = sB ∧ f.Finite := by
  sorry

end RestrictedSeries
