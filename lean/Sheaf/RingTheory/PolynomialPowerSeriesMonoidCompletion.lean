module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Sheaf.TraceFormula.SharpFsOrthantEmbedding
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Sheaf.NumberTheory.Padics.AdicInverseLimitIso
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete

/-! # Polynomial and power-series coefficients in a completed monoid algebra

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70;
the agent-supplied finite-quotient comparison of the displayed formal models
(blueprint: lem-trf-polynomial-power-series-monoid-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AddMonoidAlgebra

/-- The coefficient inclusion `L[P][T] → L[[T]][P]`: map every monoid coefficient
by the constant-series map, then evaluate each polynomial variable at the same
power-series variable in monoid degree zero. Source: ILO VI 1.6(i)--(ii), p. 70,
formal-model comparison (blueprint: lem-trf-polynomial-power-series-monoid-completion). -/
noncomputable def polynomialPowerSeriesMonoidInclusion
    (L : Type u) [CommRing L] (P : Type v) [AddCommMonoid P] (n : ℕ) :
    MvPolynomial (Fin n) (AddMonoidAlgebra L P) →+*
      AddMonoidAlgebra (MvPowerSeries (Fin n) L) P :=
  MvPolynomial.eval₂Hom
    (AddMonoidAlgebra.mapRingHom P (MvPowerSeries.C : L →+* MvPowerSeries (Fin n) L))
    (fun i ↦ algebraMap (MvPowerSeries (Fin n) L)
      (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P) (MvPowerSeries.X i))

/-- Polynomial and power-series coefficients give the same truncated formal monoid
rings and canonically the same complete local algebra, including their monomial strata.
The parameters `a`, `b`, `NB`, and `NH` are exactly the ideals specified by their equations.
`e` is induced by the displayed inclusion, `Ψ` is its inverse-limit map, and `g`
is the induced map after killing the nonconstant monomials. Composing `g` with `d`
gives the identification of the polynomial model's stratum with the coefficient series.

Source: ILO, Exposé VI 1.6(i)--(ii), printed p. 70; agent-supplied comparison of
formal models (blueprint: lem-trf-polynomial-power-series-monoid-completion).

Proof:
1. By lem-trf-sharp-fs-orthant-embedding embed the group completion of the sharp fs
   monoid in an integer orthant. The coordinate sum is positive on nonzero monoid
   elements. Apply lem-trf-positive-monoid-adic-filtration to P and P × ℕ^n.
   If ν(q) is maximal decomposition length, that length on (q,E) is ν(q)+|E|:
   use a maximal decomposition of q and the variable generators for one inequality;
   count terms with nonzero P component and then the remaining terms for the other.
   Thus membership in a^j means the coefficient at (q,E) lies in m_L^(j-ν(q)-|E|).
2. Apply the same filtration lemma over D=L[[T]] to P. Membership in b^j means
   the q coefficient belongs to m_D^(j-ν(q)). By
   lem-weil-pbc-power-series-combined-ideal-coefficients this is exactly the criterion
   of step 1, including exponent zero. Hence the inclusion has preimage b^j=a^j.
3. Truncate each of the finitely many series coefficients at total degree j.
   There are finitely many monomials of degree below j, also with zero variables.
   The discarded part lies in m_D^j by the combined-ideal coefficient lemma.
   This proves surjectivity on quotients. The same inclusion induces all levels,
   so their isomorphisms commute with the quotient reductions.
4. Apply lem-trf-adic-inverse-limit-iso to obtain Ψ with the stated projection
   identities. Its inverse is induced by the inverse level maps. The maps fix L,
   every monomial, and every variable, as these identities hold at every level.
   Both preserve the kernels of the projections, giving continuity both ways.
5. Choose finitely many nonzero generators of P, allowing the empty list. Their
   monomials generate all nonconstant monomials. Adding the variables and, for a
   Cohen ring, p, shows a and b are finitely generated. Apply
   lem-weil-pbc-module-completion-complete to obtain completeness and identify the
   projection kernels with powers of the extended ideals. Expanding products of
   generators identifies the module and ring ideal powers, so these are precisely
   the adic topologies used below.
6. By lem-weil-pbc-power-series-field-cohen-regular-complete, D is a nonzero
   Noetherian complete local ring. Apply lem-trf-formal-monoid-residue-domain to D
   and P with the lattice and positive weight from step 1. It makes H local, and
   gives its surjective constant-P-coefficient map to D with kernel NH, identical
   on D. Since Ψ is surjective and fixes monomials, it maps NB onto NH. Transport
   locality to B and pass to the quotient to obtain g and d. Their composite fixes
   L and every variable because Ψ fixes them and d is identical on D.
7. For P={0}, the list of nonzero monoid generators is empty and NB=NH=0.
   For n=0, there is only exponent zero, D=L, and coefficient truncation retains
   every coefficient. These arguments also apply when both cases occur together.
-/
theorem polynomial_power_series_monoid_completion
    (L : Type u) [CommRing L] [IsLocalRing L]
    (hL : IsField L ∨ ∃ p : ℕ, IsCohenRing p L)
    (P : Type v) [AddCommMonoid P]
    (hP : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ q : P, IsUnit (Multiplicative.ofAdd q) → q = 0)
    (n : ℕ)
    (a : Ideal (MvPolynomial (Fin n) (AddMonoidAlgebra L P)))
    (ha : a = Ideal.map (algebraMap L (MvPolynomial (Fin n) (AddMonoidAlgebra L P)))
        (IsLocalRing.maximalIdeal L) ⊔
      (Ideal.span {x | ∃ q : P, q ≠ 0 ∧ x = MvPolynomial.C (single q (1 : L))} ⊔
        Ideal.span (Set.range
          (MvPolynomial.X : Fin n → MvPolynomial (Fin n) (AddMonoidAlgebra L P)))))
    (b : Ideal (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P))
    (hb : b = Ideal.map
        (algebraMap (MvPowerSeries (Fin n) L)
          (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P))
        (Ideal.map (MvPowerSeries.C : L →+* MvPowerSeries (Fin n) L)
            (IsLocalRing.maximalIdeal L) ⊔
          Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) L))) ⊔
      Ideal.span {x | ∃ q : P, q ≠ 0 ∧ x = single q (1 : MvPowerSeries (Fin n) L)})
    (NB : Ideal (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P))))
    (hNB : NB = Ideal.span {x | ∃ q : P, q ≠ 0 ∧
      x = AdicCompletion.of a (MvPolynomial (Fin n) (AddMonoidAlgebra L P))
        (MvPolynomial.C (single q (1 : L)))})
    (NH : Ideal (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)))
    (hNH : NH = Ideal.span {x | ∃ q : P, q ≠ 0 ∧
      x = AdicCompletion.of b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)
        (single q (1 : MvPowerSeries (Fin n) L))}) :
    ∃ e : ∀ j : ℕ, 0 < j →
        (MvPolynomial (Fin n) (AddMonoidAlgebra L P) ⧸ a ^ j) ≃+*
          (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P ⧸ b ^ j),
      (∀ (j : ℕ) (hj : 0 < j) (F : MvPolynomial (Fin n) (AddMonoidAlgebra L P)),
        e j hj (Ideal.Quotient.mk (a ^ j) F) =
          Ideal.Quotient.mk (b ^ j) (polynomialPowerSeriesMonoidInclusion L P n F)) ∧
      (∀ (j : ℕ) (hj : 0 < j)
          (x : MvPolynomial (Fin n) (AddMonoidAlgebra L P) ⧸ a ^ (j + 1)),
        Ideal.Quotient.factorPow b (Nat.le_succ j) (e (j + 1) (Nat.succ_pos j) x) =
          e j hj (Ideal.Quotient.factorPow a (Nat.le_succ j) x)) ∧
      IsLocalRing (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P))) ∧
      IsLocalRing (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)) ∧
      IsAdicComplete (Ideal.map
        (algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra L P))
          (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)))) a)
        (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P))) ∧
      IsAdicComplete (Ideal.map
        (algebraMap (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)
          (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P))) b)
        (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)) ∧
      ∃ Ψ : AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)) ≃ₐ[L]
          AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P),
        (∀ (j : ℕ) (hj : 0 < j)
            (x : AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P))),
          AdicCompletion.evalₐ b j (Ψ x) = e j hj (AdicCompletion.evalₐ a j x)) ∧
        (∀ F : MvPolynomial (Fin n) (AddMonoidAlgebra L P),
          Ψ (AdicCompletion.of a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)) F) =
            AdicCompletion.of b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)
              (polynomialPowerSeriesMonoidInclusion L P n F)) ∧
        @Continuous _ _
          (Ideal.map (algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra L P))
            (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)))) a).adicTopology
          (Ideal.map (algebraMap (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)
            (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P))) b).adicTopology
          Ψ ∧
        @Continuous _ _
          (Ideal.map (algebraMap (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)
            (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P))) b).adicTopology
          (Ideal.map (algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra L P))
            (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)))) a).adicTopology
          Ψ.symm ∧
        Ideal.map Ψ.toRingEquiv.toRingHom NB = NH ∧
        ∃ g : (AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)) ⧸ NB) ≃ₐ[L]
            (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P) ⧸ NH),
          (∀ x : AdicCompletion a (MvPolynomial (Fin n) (AddMonoidAlgebra L P)),
            g (Ideal.Quotient.mk NB x) = Ideal.Quotient.mk NH (Ψ x)) ∧
          ∃ d : (AdicCompletion b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P) ⧸ NH) ≃ₐ[L]
              MvPowerSeries (Fin n) L,
            ∀ F : MvPowerSeries (Fin n) L,
              d (Ideal.Quotient.mk NH
                (AdicCompletion.of b (AddMonoidAlgebra (MvPowerSeries (Fin n) L) P)
                  (single 0 F))) = F := by
  sorry

end AddMonoidAlgebra
