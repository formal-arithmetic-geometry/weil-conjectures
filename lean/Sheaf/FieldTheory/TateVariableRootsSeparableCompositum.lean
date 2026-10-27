module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Algebraic.Integral
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Variable roots and separability of finite Tate fraction-field extensions

Source: Kedlaya, More on affinoid algebras, Theorem 4 proof, p. 2, part (a),
https://kskedlaya.org/18.727/spectra2.pdf. The general finite-extension preparation
is agent-formulated, using Stacks Tags 09H0, 09H1 and 09HC.
(blueprint: lem-trf-tate-variable-roots-separable-compositum).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- A sufficiently large characteristic-power expansion of the Tate variables makes the
compositum with a given finite fraction-field extension finite and separable.

Source: Kedlaya, More on affinoid algebras, Theorem 4 proof, p. 2, part (a),
with agent-formulated finite-extension preparation; Stacks Tags 09H0, 09H1 and 09HC.
(blueprint: lem-trf-tate-variable-roots-separable-compositum).

Proof plan:
1. The power-series domain theorem makes the restricted subrings domains. Choose a finite
fraction-field basis of L; its elements are algebraic and generate L as a field.
2. In characteristic zero use the irreducible derivative criterion and q = 1. In positive
characteristic use Polynomial.exists_separable_of_irreducible on each minimal polynomial,
and take the maximum inseparability exponent e, with q = p^e.
3. Expansion preserves restrictedness and is injective by its coefficients. Group any
series by the residue classes of its exponents modulo q; the resulting restricted series
are the unique coordinates in the asserted monomial basis. For d = 0 the empty exponent
is the only index and its monomial is 1.
4. In characteristic p, the coefficientwise q-th power map from the new Tate ring to the
old is an isomorphism: algebraic closedness gives unique coefficient roots, and the norm
identity for roots preserves restrictedness. The power-series Frobenius coefficient
formula gives b^q = iota(theta(b)). Extend theta to fraction fields.
5. Map a new fraction z into Omega by the unique q-th root of theta(z). Frobenius identities
give a field embedding extending the old fraction field. Its image consists of the
q-th roots of old fractions and hence contains all p^m-th roots for m <= e.
6. Apply these coefficient-root maps to the separable contractions of the minimal
polynomials. Transport their Bezout identities with their derivatives to obtain separable
polynomials annihilating the original generators; their minimal polynomials divide these
and are therefore separable.
7. In characteristic zero the generators are already separable. In either case the
separable-generated scalar-extension theorem makes their generated field separable over
the embedded new fraction field.
8. The span over the new fraction field of the original finite basis is a finite domain:
its multiplication is closed because the old multiplication constants lie in the new
base. Its fraction field is the compositum, and the finite-domain fraction-degree theorem
proves finiteness. No perfectness assertion about the old fraction field is used.
-/
theorem exists_tate_variable_roots_separable_compositum
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (d : ℕ)
    (L : Type v) [Field L]
    [Algebra (FractionRing
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ)))) L]
    [FiniteDimensional (FractionRing
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ)))) L]
    (Ω : Type w) [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] :
    ∃ (q : ℕ) (hq : q ≠ 0),
      0 < q ∧ (ringChar K = 0 → q = 1) ∧
      (∀ p : ℕ, p.Prime → ringChar K = p → ∃ e : ℕ, q = p ^ e) ∧
      ∃ iota :
        (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) →+*
        (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))),
        (∀ s, (iota s).val = MvPowerSeries.expand q hq s.val) ∧
        Function.Injective iota ∧
        (∃ b : @Module.Basis (Fin d → Fin q)
          (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ)))
          (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ)))
          _ _ iota.toAlgebra.toModule,
          ∀ α, (b α).val = MvPowerSeries.monomial
            (Finsupp.equivFunOnFinite.symm (fun i : Fin d ↦ (α i).val)) (1 : K)) ∧
        ∃ j : FractionRing
          (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) →+* Ω,
          (∀ s, j (algebraMap _ _ (iota s)) =
            algebraMap L Ω (algebraMap _ L (algebraMap _ (FractionRing
              (MvPowerSeries.IsRestricted.subring (R := K)
                (fun _ : Fin d ↦ (1 : ℝ)))) s))) ∧
          ∃ (E : IntermediateField L Ω) (k : FractionRing
            (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) →+* E),
            E.toSubfield = (algebraMap L Ω).fieldRange ⊔ j.fieldRange ∧
            E.val.toRingHom.comp k = j ∧
            @FiniteDimensional _ E _ _ k.toAlgebra.toModule ∧
            @Algebra.IsSeparable _ E _ _ k.toAlgebra := by
  sorry

end RestrictedSeries
