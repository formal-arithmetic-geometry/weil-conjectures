module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import Sheaf.NumberTheory.Padics.AdicInverseLimitIso
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.LocalCompletionQuotient

/-! # Completion of a polynomial nodal model

Source: Stacks Project, Curves, Tag 0CBY, first proof, third paragraph
(blueprint: lem-trf-nodal-polynomial-model-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u

noncomputable section

namespace NodalPolynomialModel

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The origin ideal, expressed by constant-term evaluation modulo the maximal ideal.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev originIdeal : Ideal (MvPolynomial (Fin 2) A) :=
  Ideal.comap MvPolynomial.constantCoeff (IsLocalRing.maximalIdeal A)

/-- The localization of the polynomial ring at its origin.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev localPolynomialRing := Localization.AtPrime (originIdeal A)

/-- The extended origin ideal in the localization.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev localOriginIdeal : Ideal (localPolynomialRing A) :=
  (originIdeal A).map (algebraMap (MvPolynomial (Fin 2) A) (localPolynomialRing A))

/-- The combined coefficient and variable ideal in the series ring.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev seriesOriginIdeal : Ideal (MvPowerSeries (Fin 2) A) :=
  (IsLocalRing.maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin 2) A)) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) A))

/-- The defining equation of the polynomial model.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev equation (h : A) : MvPolynomial (Fin 2) A :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C h

/-- The affine nodal model's coordinate ring.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev modelRing (h : A) := MvPolynomial (Fin 2) A ⧸ Ideal.span {equation A h}

/-- The local ring of the actual affine scheme at a point.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev modelStalk (h : A) (o : PrimeSpectrum (modelRing A h)) :=
  (AlgebraicGeometry.Spec (CommRingCat.of (modelRing A h))).presheaf.stalk o

/-- The coefficient algebra structure on the model's stalk, using its canonical germ map.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
instance modelStalkAlgebra (h : A) (o : PrimeSpectrum (modelRing A h)) :
    Algebra A (modelStalk A h o) :=
  ((AlgebraicGeometry.StructureSheaf.toStalk (modelRing A h) o).hom.comp
    (algebraMap A (modelRing A h))).toAlgebra

/-- The germ of a polynomial on the affine model.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
def polynomialGerm (h : A) (o : PrimeSpectrum (modelRing A h)) :
    MvPolynomial (Fin 2) A →+* modelStalk A h o :=
  (AlgebraicGeometry.StructureSheaf.toStalk (modelRing A h) o).hom.comp
    (Ideal.Quotient.mk (Ideal.span {equation A h}))

/-- The localized hypersurface quotient `D/(xy-h)D`.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev localModelRing (h : A) :=
  localPolynomialRing A ⧸ Ideal.span
    {algebraMap (MvPolynomial (Fin 2) A) (localPolynomialRing A) (equation A h)}

/-- The formal hypersurface quotient `A[[x,y]]/(xy-h)`.
Source: Stacks Tag 0CBY (blueprint: lem-trf-nodal-polynomial-model-completion). -/
abbrev seriesModelRing (h : A) :=
  MvPowerSeries (Fin 2) A ⧸ Ideal.span {(equation A h : MvPowerSeries (Fin 2) A)}

/-- The polynomial nodal model has the asserted finite quotients, stalk, residue field,
and completed local equation, with all comparisons induced by the coefficient/variable maps.

Source: Stacks Project, Curves, Tag 0CBY, first proof, third paragraph, the completed
local ring of `Y_sigma` (blueprint: lem-trf-nodal-polynomial-model-completion).

Proof:
1. Constant-term evaluation modulo the maximal ideal has kernel `(m,x,y)` and is
   surjective onto `A/m`, so the origin ideal is maximal. Localization identifies its
   extension with the maximal ideal of `D` (def-weil-pbc-localization-at-prime).
2. Expand `q^r` as the sum of `m^(r-j)(x,y)^j`. A polynomial belongs to it exactly
   when its coefficient at each exponent `E` of degree below `r` belongs to
   `m^(r-degree E)`: check each summand for necessity and each monomial for sufficiency.
3. The same coefficient criterion for series is
   lem-weil-pbc-power-series-combined-ideal-coefficients. Hence inclusion induces an
   injection on the quotients; truncation below total degree `r` gives surjectivity.
4. Each denominator outside `q` has unit constant term `c`. Its remaining part `t`
   has zero constant term. Modulo `q^r`, the finite geometric sum
   `c^(-1) * sum_{j<r} (-t/c)^j` is its inverse. The localization universal property
   supplies the inverse to the polynomial-to-localization quotient map `v_r`.
5. The infinite geometric sum is well defined coefficientwise (only finitely many
   terms contribute in each degree) and inverts that denominator in the series ring.
   This defines `j : D -> A[[x,y]]`, and its quotient maps `w_r` are isomorphisms since
   their composites with `v_r` are the isomorphisms from step 3.
6. All quotient maps send a polynomial to its own class and a fraction to the numerator
   times the inverse denominator. These formulas verify both transition squares and
   preserve coefficients and each of the two variables.
7. Apply lem-trf-adic-inverse-limit-iso to the compatible `w_r`. By
   lem-weil-pbc-power-series-complete-over-complete-base and
   def-weil-pbc-adically-complete-ring the series ring equals its combined-adic completion.
   Thus the resulting `e` has the displayed projections. Separatedness shows that
   `e` sends the completion image of `d` to `j(d)`, so it is an A-algebra comparison.
8. Since `h` belongs to `m`, the equation belongs to `q`. Its quotient defines the
   origin point on the affine model. Apply lem-weil-pbc-affine-open-stalk-localization
   and lem-weil-pbc-localization-at-prime-of-quotient to identify the stalk with
   `D/(xy-h)D`, sending polynomial germs to polynomial classes. Modulo the maximal
   ideal this is `A/m`, through the coefficient map (def-weil-residue-field).
9. The polynomial ring and its localization are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-localization-noetherian.
   Apply lem-weil-pbc-local-completion-quotient to `D -> D/(xy-h)D`. Its canonical
   quotient-completion comparison commutes with completion maps. Under `e` the equation
   is still `xy-h`. Passing to its quotient gives the completed-stalk comparison `E`;
   the commutation identity proves its normalization on constants and variables.
-/
theorem nodal_polynomial_model_completion
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (h : A) (hh : h ∈ IsLocalRing.maximalIdeal A) :
    originIdeal A =
      (IsLocalRing.maximalIdeal A).map (algebraMap A (MvPolynomial (Fin 2) A)) ⊔
        Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) A)) ∧
    (originIdeal A).IsMaximal ∧
    localOriginIdeal A = IsLocalRing.maximalIdeal (localPolynomialRing A) ∧
    ∃ j : localPolynomialRing A →ₐ[A] MvPowerSeries (Fin 2) A,
      (∀ p : MvPolynomial (Fin 2) A,
        j (algebraMap (MvPolynomial (Fin 2) A) (localPolynomialRing A) p) =
          (p : MvPowerSeries (Fin 2) A)) ∧
      ∃ (v : ∀ r : ℕ, 0 < r →
          (MvPolynomial (Fin 2) A ⧸ originIdeal A ^ r) ≃ₐ[A]
            (localPolynomialRing A ⧸ localOriginIdeal A ^ r))
        (w : ∀ r : ℕ, 0 < r →
          (localPolynomialRing A ⧸ localOriginIdeal A ^ r) ≃ₐ[A]
            (MvPowerSeries (Fin 2) A ⧸ seriesOriginIdeal A ^ r)),
        (∀ (r : ℕ) (hr : 0 < r) (p : MvPolynomial (Fin 2) A),
          v r hr (Ideal.Quotient.mk _ p) =
            Ideal.Quotient.mk _
              (algebraMap (MvPolynomial (Fin 2) A) (localPolynomialRing A) p)) ∧
        (∀ (r : ℕ) (hr : 0 < r) (d : localPolynomialRing A),
          w r hr (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (j d)) ∧
        (∀ (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
            (z : MvPolynomial (Fin 2) A ⧸ originIdeal A ^ r),
          Ideal.Quotient.factorPow (localOriginIdeal A) hsr (v r hr z) =
            v s hs (Ideal.Quotient.factorPow (originIdeal A) hsr z)) ∧
        (∀ (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
            (z : localPolynomialRing A ⧸ localOriginIdeal A ^ r),
          Ideal.Quotient.factorPow (seriesOriginIdeal A) hsr (w r hr z) =
            w s hs (Ideal.Quotient.factorPow (localOriginIdeal A) hsr z)) ∧
        ∃ e : AdicCompletion (localOriginIdeal A) (localPolynomialRing A) ≃ₐ[A]
            MvPowerSeries (Fin 2) A,
          (∀ d : localPolynomialRing A,
            e (AdicCompletion.of (localOriginIdeal A) (localPolynomialRing A) d) = j d) ∧
          (∀ (r : ℕ) (hr : 0 < r)
              (z : AdicCompletion (localOriginIdeal A) (localPolynomialRing A)),
            Ideal.Quotient.mk (seriesOriginIdeal A ^ r) (e z) =
              w r hr (AdicCompletion.evalₐ (localOriginIdeal A) r z)) ∧
          ∃ o : PrimeSpectrum (modelRing A h),
            o.asIdeal = (originIdeal A).map (Ideal.Quotient.mk (Ideal.span {equation A h})) ∧
            ∃ b : modelStalk A h o ≃ₐ[A] localModelRing A h,
              (∀ p : MvPolynomial (Fin 2) A,
                b (polynomialGerm A h o p) = Ideal.Quotient.mk _
                  (algebraMap (MvPolynomial (Fin 2) A) (localPolynomialRing A) p)) ∧
              ∃ ρ :
                  (AlgebraicGeometry.Spec (CommRingCat.of (modelRing A h))).residueField o ≃+*
                    IsLocalRing.ResidueField A,
                (∀ a : A,
                  ρ (IsLocalRing.residue (modelStalk A h o)
                    (polynomialGerm A h o (MvPolynomial.C a))) = IsLocalRing.residue A a) ∧
                ∃ E : AdicCompletion (IsLocalRing.maximalIdeal (modelStalk A h o))
                    (modelStalk A h o) ≃ₐ[A] seriesModelRing A h,
                  ∀ p : MvPolynomial (Fin 2) A,
                    E (AdicCompletion.of (IsLocalRing.maximalIdeal (modelStalk A h o))
                      (modelStalk A h o) (polynomialGerm A h o p)) =
                        Ideal.Quotient.mk _ (p : MvPowerSeries (Fin 2) A) := by
  sorry

end NodalPolynomialModel
