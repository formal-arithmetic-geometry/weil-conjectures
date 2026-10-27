module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Defs

import Mathlib.RingTheory.Ideal.Maximal

/-!
# Supremum seminorm estimates on affinoid algebras

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2 Corollary 11,
Section 1.4, definition before Proposition 5 and Propositions 5--8, pp. 23--24;
Appendix Corollary 2 and Theorem 3
(blueprint: lem-trf-affinoid-supremum-seminorm-calculus).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- The residue values at all maximal ideals, using all extending absolute values.
For an affinoid algebra the theorem below asserts existence and uniqueness of the
extension, so this is exactly the set indexed by its maximal ideals, without choices.
Source: Bosch, Section 1.4, definition before Proposition 5, p. 23
(blueprint: lem-trf-affinoid-supremum-seminorm-calculus). -/
def affinoidResidueValues
    (K : Type u) [NormedField K] (A : Type v) [CommRing A]
    (scalar : K →+* A) (a : A) : Set ℝ :=
  {t | ∃ (m : Ideal A), m.IsMaximal ∧
    ∃ v : AbsoluteValue (A ⧸ m) ℝ,
      (∀ c : K, v (Ideal.Quotient.mk m (scalar c)) = ‖c‖) ∧
      t = v (Ideal.Quotient.mk m a)}

/-- The supremum of maximal residue absolute values. Boundedness and the least-upper-bound
property are conclusions of `affinoid_supremum_seminorm_calculus`, not assumptions or choices.
Source: Bosch, Section 1.4, definition before Proposition 5, p. 23
(blueprint: lem-trf-affinoid-supremum-seminorm-calculus). -/
noncomputable def affinoidSupremum
    (K : Type u) [NormedField K] (A : Type v) [CommRing A]
    (scalar : K →+* A) (a : A) : ℝ :=
  sSup (affinoidResidueValues K A scalar a)

/-- Supremum seminorm calculus for algebraic affinoid presentations, with no norm or
reducedness imposed on the quotient algebra and no continuity imposed on homomorphisms.
Source: Bosch, Section 1.2 Corollary 11; Section 1.4, definition before Proposition 5 and
Propositions 5--8, pp. 23--24; Appendix Corollary 2 and Theorem 3
(blueprint: lem-trf-affinoid-supremum-seminorm-calculus).

Proof:
1. Pull a maximal ideal back along a surjective Tate presentation. The resulting residue
field is finite over K and has a unique extending absolute value by
lem-per-tate-maximal-residue-evaluation and the Appendix extension theorem. A nonzero
ring has a maximal ideal by lem-weil-pbc-proper-ideal-contained-in-maximal.
2. Its coordinate residues have absolute value at most one. The convergent evaluation
formula and lem-per-tate-banach-substitution bound every residue value of a lift by its
Gauss norm. Hence the nonempty set of residue values is bounded above and its supremum
is a finite nonnegative real number.
3. Take the infimum over all lifts to obtain the bound for every surjective presentation.
4. Residue absolute values commute with positive integral powers. Taking suprema gives
the upper power bound. If the reverse inequality failed, continuity of the positive power
function would give a smaller putative upper bound for the residue values, a contradiction.
Nilpotents map to zero in every residue field, so their supremum is zero.
5. For a homomorphism B to A, the quotient of B by the inverse image of a maximal ideal
embeds into the finite K-field A/m. It is a finite-dimensional domain and thus a field.
Uniqueness of extending absolute values identifies the two residue values. Taking their
suprema proves contractivity, without assuming continuity.
6. On a Tate algebra, the identity presentation gives the Gauss upper bound. For a nonzero
series choose a coefficient attaining its Gauss norm and divide by it, giving g of norm one.
In one more variable, 1-Yg is a nonunit by lem-trf-tate-unit-coefficient-criterion. Put it
in a maximal ideal using lem-weil-pbc-proper-ideal-contained-in-maximal. The residue
evaluation of lem-per-tate-maximal-residue-evaluation gives y*g(x)=1 with both factors
of absolute value at most one. Thus g(x) has absolute value one. Substitution on the
original variables (lem-per-tate-banach-substitution) has finite-dimensional domain image
inside that residue field; its image is a field and its kernel is maximal. This maximal
residue value attains the Gauss norm of the original series. The zero series is immediate,
and the same argument includes zero variables. -/
theorem affinoid_supremum_seminorm_calculus
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Nontrivial A] [Algebra K A]
    (hA : ∃ (r : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* A),
      Function.Surjective q ∧ q.comp (constants K r) = algebraMap K A) :
    (∀ (m : Ideal A), m.IsMaximal →
      Module.Finite K (A ⧸ m) ∧
      ∃! v : AbsoluteValue (A ⧸ m) ℝ,
        ∀ c : K, v (Ideal.Quotient.mk m (algebraMap K A c)) = ‖c‖) ∧
    (∀ a : A,
      IsLUB (affinoidResidueValues K A (algebraMap K A) a)
        (affinoidSupremum K A (algebraMap K A) a) ∧
      0 ≤ affinoidSupremum K A (algebraMap K A) a ∧
      ∀ n : ℕ, 1 ≤ n →
        affinoidSupremum K A (algebraMap K A) (a ^ n) =
          affinoidSupremum K A (algebraMap K A) a ^ n) ∧
    (∀ (r : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* A),
      Function.Surjective q → q.comp (constants K r) = algebraMap K A →
      ∀ a : A, affinoidSupremum K A (algebraMap K A) a ≤
        sInf {t : ℝ | ∃ f, q f = a ∧
          t = MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) f.val}) ∧
    (∀ (B : Type w) [CommRing B] [Nontrivial B] [Algebra K B],
      (∃ (r : ℕ)
        (q : (MvPowerSeries.IsRestricted.subring (R := K)
          (fun _ : Fin r ↦ (1 : ℝ))) →+* B),
        Function.Surjective q ∧ q.comp (constants K r) = algebraMap K B) →
      ∀ (ψ : B →ₐ[K] A) (b : B),
        affinoidSupremum K A (algebraMap K A) (ψ b) ≤
          affinoidSupremum K B (algebraMap K B) b) ∧
    (∀ (d : ℕ)
      (f : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))),
      affinoidSupremum K _ (constants K d) f =
        MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin d ↦ 1) f.val) ∧
    (∀ a : A, IsNilpotent a → affinoidSupremum K A (algebraMap K A) a = 0) := by
  sorry

end RestrictedSeries
