module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.Finite
import WeilConjectures.RingTheory.FibrePrimesResidueFields
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Sheaf.TraceFormula.RefinedNoetherNormalizationPrime

/-!+# Lifting normalized polynomial coordinates at a prime

Source: Stacks Project, Algebra, Tags 0520 and 051P, the image fibre prime and
the lifting of normalized coordinates (blueprint: lem-trf-normalized-polynomial-prime-lift).

The auxiliary maps spell out the canonical residue-field evaluation, coefficient
map from a principal localization, and reduction of a polynomial algebra map.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

/-- The image fibre prime, expressed in polynomial coordinates as the kernel of
evaluation in the residue field of `q`. The coefficient map is the canonical
embedding of residue fields induced by contraction.
Source: Stacks Project, Algebra, Tag 0520, the prime `q̄'` in its proof
(blueprint: lem-trf-normalized-polynomial-prime-lift). -/
noncomputable def polynomialFibrePrime
    (R : Type u) [CommRing R] (n : ℕ) (p : PrimeSpectrum R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (hp : p.asIdeal = q.asIdeal.under R) :
    PrimeSpectrum (MvPolynomial (Fin n) p.asIdeal.ResidueField) :=
  ⟨RingHom.ker (MvPolynomial.eval₂Hom
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R _) hp)
      (fun i ↦ algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X i))),
    RingHom.ker_isPrime _⟩

/-- The canonical coefficient map `R_f → κ(p)` for `f ∉ p`.
Source: Stacks Project, Algebra, Tag 0520, the coefficient lifting in its proof
(blueprint: lem-trf-normalized-polynomial-prime-lift). -/
noncomputable def polynomialAwayResidueMap
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal) :
    Localization.Away f →+* p.asIdeal.ResidueField :=
  Localization.awayLift (algebraMap R p.asIdeal.ResidueField) f
    (isUnit_iff_ne_zero.mpr (mt Ideal.algebraMap_residueField_eq_zero.mp hf))

/-- Reduction of a polynomial algebra map modulo the base prime. Each variable
is sent to the coefficientwise reduction of its image, so this is its scalar
extension under the canonical polynomial scalar-extension identifications.
Source: Stacks Project, Algebra, Tag 0520, the lifted map becoming finite on the fibre
(blueprint: lem-trf-normalized-polynomial-prime-lift). -/
noncomputable def polynomialMapResidueReduction
    (R : Type u) [CommRing R] (n : ℕ) (p : PrimeSpectrum R) (f : R) (hf : f ∉ p.asIdeal)
    (ψ : MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
      MvPolynomial (Fin n) (Localization.Away f)) :
    MvPolynomial (Fin n) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
      MvPolynomial (Fin n) p.asIdeal.ResidueField :=
  MvPolynomial.aeval (fun i ↦
    MvPolynomial.map (polynomialAwayResidueMap R p f hf) (ψ (MvPolynomial.X i)))

/-- Lift normalized polynomial coordinates and compute the image prime.
Source: Stacks Project, Algebra, Tags 0520 and 051P
(blueprint: lem-trf-normalized-polynomial-prime-lift).

Proof plan:
1. The fibre-prime correspondence identifies `Q` with the kernel of residue-field
   evaluation and contracts it to `q`. Its residue field is the fraction field of
   `k[t]/Q`. The variable images generate this quotient; each fraction `a/b` is
   algebraic over it by `bT-a`. The algebraic-adjoin transcendence bound therefore
   gives a finite transcendence degree `r ≤ n`.
2. Apply refined Noether normalization (Tag 051P) to `Q`. It supplies a finite
   polynomial map whose contraction of `Q` is the ideal of the last `n-r` variables.
3. Lift the finitely many coefficients of the variable images to fractions `a/b`
   with `b ∉ p`. Their common denominator `f` is outside `p`; the empty product is
   `1`. Lift each coefficient to `ac/f` when `f=bc`.
4. Evaluation at these lifted polynomials defines `ψ`. The target variables
   generate its target as an algebra over its source, giving finite type. Under
   polynomial scalar extension its reduction is the map of step 2, hence finite
   with the prescribed inverse-image ideal.
5. The target is the localization of `R[t]` at `f`. The localization prime
   correspondence identifies `qD` with the inverse image of `Q` under coefficient
   reduction: a fraction `G/f^m` maps into `Q` exactly when `G ∈ q`. Commutativity
   with `ψ` identifies `P` with the inverse image of the coordinate ideal.
6. The kernel of `R_f → k` is `pR_f`. A polynomial reduces into the coordinate
   ideal precisely when its coefficients on monomials in the first `r` variables
   belong to this kernel. The remaining monomials are divisible by a last
   variable, giving `P = (pR_f, x_{r+1}, …, x_n)`. Contraction under coefficient
   reduction is the fibre-prime correspondence (using the localization
   residue-field isomorphism), so the last equality identifies its fibre prime.
-/
theorem normalizedPolynomialPrimeLift
    (R : Type u) [CommRing R] (n : ℕ) (p : PrimeSpectrum R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (hp : p.asIdeal = q.asIdeal.under R) :
    ∃ r : ℕ,
      Algebra.trdeg p.asIdeal.ResidueField (polynomialFibrePrime R n p q hp).asIdeal.ResidueField =
        (r : Cardinal) ∧ r ≤ n ∧
      ∃ (f : R) (hf : f ∉ p.asIdeal)
        (ψ : MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
          MvPolynomial (Fin n) (Localization.Away f)),
        ψ.toRingHom.FiniteType ∧
        (polynomialMapResidueReduction R n p f hf ψ).toRingHom.Finite ∧
        Ideal.comap (polynomialMapResidueReduction R n p f hf ψ).toRingHom
            (polynomialFibrePrime R n p q hp).asIdeal =
          Ideal.span (Set.range (fun i : Fin n ↦
            if r ≤ i.val then MvPolynomial.X i else 0)) ∧
        Ideal.comap ψ.toRingHom
            (q.asIdeal.map (MvPolynomial.map (algebraMap R (Localization.Away f)))) =
          p.asIdeal.map (MvPolynomial.C.comp (algebraMap R (Localization.Away f))) ⊔
            Ideal.span (Set.range (fun i : Fin n ↦
              if r ≤ i.val then MvPolynomial.X i else 0)) ∧
        Ideal.comap (MvPolynomial.map (polynomialAwayResidueMap R p f hf))
            (Ideal.span (Set.range (fun i : Fin n ↦
              if r ≤ i.val then MvPolynomial.X i else 0))) =
          Ideal.comap ψ.toRingHom
            (q.asIdeal.map (MvPolynomial.map (algebraMap R (Localization.Away f)))) := by
  sorry

end Algebra
