module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Distinguished presentations of reduced affinoid algebras

Source: Bosch--Guentzer--Remmert, Non-Archimedean Analysis, Theorem 6.4.3/1 and
6.4.3/6; Rodriguez Vazquez, Non-Archimedean normal families, Section 2.2,
printed p. 1685, preceding Proposition 2.2 and its proof
(blueprint: lem-trf-affinoid-distinguished-presentation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- A nonzero reduced affinoid over an algebraically closed complete nontrivially
valued nonarchimedean field has a Tate presentation mapping the integral restricted
series onto exactly the power-bounded elements.

Source: BGR, Theorem 6.4.3/1 with 6.4.3/6; Rodriguez Vazquez, Section 2.2,
printed p. 1685 (blueprint: lem-trf-affinoid-distinguished-presentation).

The hypothesis `haff` gives the quotient Gauss topology, allowing any equivalent
Banach norm on `C`. Continuity of the resulting map is expressed by Gauss balls;
the coefficientwise topology of formal power series is never used. Scalar
compatibility with `constants` makes the ring homomorphism a K-algebra map.
The coefficient condition is precisely membership in V-restricted series
inside K-restricted series, with the induced norm on V. The powers include m = 0.

Proof (the node's four steps):
1. Choose a quotient norm from an initial presentation. Apply
   lem-trf-affinoid-spectral-banach-norm to get the complete power-multiplicative
   spectral norm rho, equivalent to the quotient norm. Equivalent norms have the
   same bounded sets. Thus c is power-bounded exactly when rho(c) <= 1:
   bounded powers force rho(c)^m bounded, and the converse follows by norm equivalence.
2. By lem-trf-affinoid-canonical-reduction-finite-type, choose finitely many integral
   lifts b_j of generators of the canonical reduction. Retain the original Tate
   generators a_i, which also have spectral norm at most one by the quotient bound.
3. Apply lem-per-tate-banach-substitution to the complete spectral norm and the tuple
   (a_i, b_j). This gives a continuous map q, contractive for the spectral norm.
   The coefficient inclusion of the original Tate algebra is isometric by
   lem-trf-restricted-series-gauss-completion. Uniqueness of substitution makes q
   restrict to the original presentation, hence q is surjective.
4. The reduction of q is surjective because the classes of the b_j generate.
   Apply lem-trf-tate-reduction-norm-lifting to this particular epimorphism: every c
   has a lift with Gauss norm rho(c). For power-bounded c that norm is at most one,
   so every coefficient lies in V. Conversely integral coefficients give Gauss norm
   at most one, and contractivity makes the image power-bounded by step 1. -/
theorem affinoid_distinguished_presentation
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K]
    (V : ValuationSubring K) (hV : ∀ a : K, a ∈ V ↔ ‖a‖ ≤ 1)
    (C : Type v) [NormedCommRing C] [CompleteSpace C] [Nontrivial C] [IsReduced C]
    [Algebra K C]
    (haff : ∃ (r : ℕ)
      (q₀ : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* C),
      Function.Surjective q₀ ∧ q₀.comp (constants K r) = algebraMap K C ∧
      ∀ U : Set C, IsOpen U ↔ ∀ f, q₀ f ∈ U → ∃ ε : ℝ, 0 < ε ∧
        ∀ g, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
          (g.val - f.val) < ε → q₀ g ∈ U) :
    ∃ (s : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ (1 : ℝ))) →+* C),
      Function.Surjective q ∧ q.comp (constants K s) = algebraMap K C ∧
      (∀ f, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ g, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1)
          (g.val - f.val) < δ → ‖q g - q f‖ < ε) ∧
      ∀ c : C,
        (∃ f, (∀ ν : Fin s →₀ ℕ, MvPowerSeries.coeff ν f.val ∈ V) ∧ q f = c) ↔
          ∃ M : ℝ, ∀ m : ℕ, ‖c ^ m‖ ≤ M := by
  sorry

end RestrictedSeries
