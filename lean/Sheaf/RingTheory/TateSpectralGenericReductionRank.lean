module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Gauss homogeneity and the generic rank of affinoid reduction

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2, pp. 8--9,
and Section 1.4, Lemma 12(i)--(iii), pp. 25--27; agent reconstruction
(blueprint: lem-trf-tate-spectral-generic-reduction-rank).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

open scoped TensorProduct

namespace RestrictedSeries

/-- Gauss homogeneity, polynomial reduction, and the generic-rank bound for a finite
injective Tate-algebra map to an affinoid domain.
Source: Bosch (2008), Section 1.2, pp. 8--9, and Section 1.4, Lemma 12(i)--(iii),
pp. 25--27; agent reconstruction, not a theorem quoted verbatim from Bosch
(blueprint: lem-trf-tate-spectral-generic-reduction-rank).

The scalar map from the Tate ring is `algebraMap`; `hscalar` makes it a K-algebra map.
The formula `hρ` takes the supremum over maximal residue fields and their extending
absolute values. These extensions exist and are unique, so this is the source's
supremum, without a choice of residue-field norms. The existential subrings U and P
have exactly the displayed unit balls as carriers. The ideal I has exactly the open
unit ball as carrier; thus P/I is the source's S. The coefficient identity specifies
red, including its constants, and the last compatibility specifies the induced jbar.
Extension of scalars is written Q tensor_R S, using the symmetric convention of
Mathlib's base-change interface. Every algebra structure quantified in the final
clause is required to have structure map jbar, so that clause concerns the canonical
R-action, not an arbitrary action.

Proof (the node's seven steps).
1. Apply lem-trf-tate-fraction-orthogonal-spectral-norm to E = Frac(C). Its norm N
restricts to ρ and is homogeneous over Frac(T), whose norm restricts to the Gauss
norm G. This gives ρ(tc) = G(t)ρ(c), also for zero factors. The minimal polynomial
Z - 1 gives N(1) = 1 and hence ρ(j(t)) = G(t); no orthogonal basis is needed.
2. The residue absolute values and lem-trf-affinoid-supremum-seminorm-calculus give
ultrametricity, submultiplicativity, and the power formula for ρ. These make P a
subring and I an ideal. If a positive power of a class is zero, the power formula
shows its representative has ρ less than one; thus the class is zero.
3. By lem-trf-tate-unit-ball-polynomial-reduction, coefficient reduction is onto the
residue polynomial ring with kernel G < 1. Homogeneity embeds this quotient into
P/I. The Gauss multiplicativity of lem-trf-tate-gauss-multiplicative ensures the
polynomial ring is a domain, also directly supplied by its coefficient field.
4. Lift nonzero r and s in the polynomial ring and P/I to t and c of norms one.
Homogeneity makes ρ(j(t)c) = 1, so rs is nonzero. This proves torsion-freeness.
5. By lem-weil-pbc-localization-base-change, scalar extension to Q is localization
at the nonzero polynomials. Clear each denominator of a finite Q-independent
family to obtain independent vectors s_i tensor 1, and lift each s_i to c_i in P.
6. A nonzero Frac(T)-linear relation among the c_i clears to a T-linear relation.
The largest coefficient of its finitely many restricted series is attained.
Dividing by that coefficient gives Gauss norms at most one, with one equal to one.
Coefficient reduction then gives a nonzero Q-linear relation among s_i tensor 1,
contradicting independence. Thus the c_i are Frac(T)-independent.
7. By lem-weil-independent-family-card-le-dimension, the size of this family is at
most [E:F]. Repeatedly adjoining a vector outside the span therefore stops by that
bound and gives a finite basis of Q tensor_R S of dimension at most [E:F]. No
integrality or module finiteness of S over R is asserted. -/
theorem tate_spectral_generic_reduction_rank
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (d : ℕ)
    (V : ValuationSubring K) (hV : ∀ a : K, a ∈ V ↔ ‖a‖ ≤ 1)
    (C : Type v) [CommRing C] [IsDomain C] [Algebra K C]
    [Algebra (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) C]
    [Module.Finite
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) C]
    (hinj : Function.Injective (algebraMap
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) C))
    (hscalar : (algebraMap
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) C).comp
        (constants K d) = algebraMap K C)
    (haff : ∃ (n : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ (1 : ℝ))) →+* C),
      Function.Surjective q ∧ q.comp (constants K n) = algebraMap K C)
    (ρ : C → ℝ)
    (hρ : ∀ c : C, ρ c = sSup {r : ℝ | ∃ m : MaximalSpectrum C,
      ∃ a : AbsoluteValue (C ⧸ m.asIdeal) ℝ,
        (∀ b : K, a (Ideal.Quotient.mk m.asIdeal (algebraMap K C b)) = ‖b‖) ∧
        r = a (Ideal.Quotient.mk m.asIdeal c)}) :
    (∀ (t : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ)))
      (c : C),
      ρ (algebraMap _ C t * c) =
        MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin d ↦ 1) t.val * ρ c) ∧
    ∃ U : Subring
        (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))),
      (∀ t, t ∈ U ↔
        MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin d ↦ 1) t.val ≤ 1) ∧
      ∃ (red : U →+* MvPolynomial (Fin d) (IsLocalRing.ResidueField V)),
        Function.Surjective red ∧
        (∀ t : U, red t = 0 ↔
          MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin d ↦ 1) t.val.val < 1) ∧
        (∀ (t : U) (m : Fin d →₀ ℕ), ∃ a : V,
          a.val = MvPowerSeries.coeff m t.val.val ∧
          MvPolynomial.coeff m (red t) = IsLocalRing.residue V a) ∧
        ∃ P : Subring C, (∀ c : C, c ∈ P ↔ ρ c ≤ 1) ∧
          ∃ I : Ideal P, (∀ c : P, c ∈ I ↔ ρ c.val < 1) ∧
            IsReduced (P ⧸ I) ∧
            ∃ (jU : U →+* P)
              (jbar : MvPolynomial (Fin d) (IsLocalRing.ResidueField V) →+* P ⧸ I),
              (∀ t : U, (jU t).val = algebraMap _ C t.val) ∧
              Function.Injective jbar ∧
              (∀ t : U, jbar (red t) = Ideal.Quotient.mk I (jU t)) ∧
              ∀ [A : Algebra (MvPolynomial (Fin d) (IsLocalRing.ResidueField V)) (P ⧸ I)],
                algebraMap (MvPolynomial (Fin d) (IsLocalRing.ResidueField V)) (P ⧸ I) =
                  jbar →
                (∀ (r : MvPolynomial (Fin d) (IsLocalRing.ResidueField V)) (s : P ⧸ I),
                  r ≠ 0 → r • s = 0 → s = 0) ∧
                FiniteDimensional
                  (FractionRing (MvPolynomial (Fin d) (IsLocalRing.ResidueField V)))
                  ((FractionRing (MvPolynomial (Fin d) (IsLocalRing.ResidueField V))) ⊗[
                    MvPolynomial (Fin d) (IsLocalRing.ResidueField V)] (P ⧸ I)) ∧
                Module.finrank
                    (FractionRing (MvPolynomial (Fin d) (IsLocalRing.ResidueField V)))
                    ((FractionRing (MvPolynomial (Fin d) (IsLocalRing.ResidueField V))) ⊗[
                      MvPolynomial (Fin d) (IsLocalRing.ResidueField V)] (P ⧸ I)) ≤
                  @Module.finrank
                    (FractionRing (MvPowerSeries.IsRestricted.subring (R := K)
                      (fun _ : Fin d ↦ (1 : ℝ))))
                    (FractionRing C) _ _
                    (IsFractionRing.map (K := FractionRing
                      (MvPowerSeries.IsRestricted.subring (R := K)
                        (fun _ : Fin d ↦ (1 : ℝ))))
                      (L := FractionRing C) hinj).toAlgebra.toModule := by
  sorry

end RestrictedSeries
