/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.PermissibleBasisChartData
public import WeilConjectures.RingTheory.ProjectiveConeHilbertStandardDegrees
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.RegularSequenceGradedPolynomial
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-! # Adapted standard bases without reducedness

Source: Hironaka, Certain numerical characters of singularities (1970),
Proposition 21(i)-(ii), p.181, and Lemma 20, pp.175-181.
(blueprint: lem-per-permissible-adapted-standard-basis).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Hironaka

open AlgebraicGeometry AlgebraicGeometry.AffineBlowup AlgebraicGeometry.NodalLocal

/-- Equality of the minimal homogeneous generator degree sequences gives an adapted
standard basis at the specified permissible chart point. The chart and parameter maps
are fixed on all generators by their recorded predicates. No reducedness is assumed.
The ratio labels are the nonzero members of `Fin (r + 1)`, giving exactly `r` variables.

Source: Hironaka (1970), Proposition 21(i)-(ii), p.181, under (2.1)-(2.2).
(blueprint: lem-per-permissible-adapted-standard-basis).

Proof, following the eleven steps of the node:
1. Apply lem-trf-normal-flat-double-initial-ideal to identify the tangent initial
ideal with the extension of the normal-cone fibre kernel C in k[X]. Its degree-zero
part is zero since the degree-zero map on k is the identity.
2. The polynomial ring is Noetherian by lem-wf-affine-noetherian-components.
Choose homogeneous ideal generators, remove redundant ones and order their degrees.
Their residues form a basis modulo the positive-degree ideal times C, by degree induction.
3. Extending to k[X,Y] preserves minimality by setting Y to zero. The degrees are
therefore nuStar. If the family is empty, Krull intersection
(lem-weil-pbc-krull-intersection-jacobson) implies b = 0, giving the empty answer.
4. The parameter list is regular by lem-weil-pbc-regular-local-generators-regular-sequence.
Its x-prefix is regular using def-weil-pbc-regular-sequence. Apply
lem-pur-regular-sequence-graded-polynomial to identify gr_P T with (T/P)[X].
5. Every graded piece of gr_I R is flat as a direct summand. Apply
lem-weil-pbc-flat-quotient-tensor-injective to lift the degree-d fibre kernel to the
kernel over T/P. Lift the residue coefficients of each chosen homogeneous generator.
6. Evaluate a lifted degree-d polynomial in x to obtain an element of P^d. Its
image in R lies in I^(d+1); subtract a lift from P^(d+1). This gives an element
of b with the desired nonzero initial form and exact maximal-ideal order d.
7. By lem-trf-parameter-blowup-algebra-regular the ambient chart embeds in T[1/x0].
Divide the lifted generators by their x0 powers, using their degree-d monomial
expansions. Define H = (x0,y) and the order spaces U_d of the chart fibre prime.
8. Induct through the finite ordered family, keeping exact original orders,
minimal homogeneous initial generation and, for each earlier index, membership in
U_d and a divided transform of order d after subtraction of an earlier H-combination.
9. Apply lem-per-permissible-standard-basis-one-step, which imposes no reducedness,
at the current index. Equality of nuStar supplies its numerical hypothesis. Replace
that generator by its triangular correction and retain the resulting earlier correction.
10. The corrections stay in b and P^d. The triangular change is invertible and
induces an invertible change on the indecomposable homogeneous generators, preserving
minimality and all earlier assertions. The corrected initial form belongs to k[X].
11. After the last index discard the divided transforms and their corrections.
The remaining generators have precisely the asserted orders and initial forms;
U_d gives the stated localized dehomogenization condition, including nonrational primes.
-/
theorem permissibleAdaptedStandardBasis
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (r s : ℕ) (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (b : Ideal T) (hb : b ≤ Ideal.span (Set.range x))
    (hflat : Module.Flat
      ((T ⧸ b) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))))
    (hmin : ∀ q ∈ minimalPrimes (T ⧸ b),
      ¬ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b) ≤ q)
    (ρ : ParameterChart x →+*
      chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
        (Ideal.Quotient.mk b (x 0))) (hρ : IsQuotientChartMap x b ρ)
    (z : PrimeSpectrum (chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.Quotient.mk b (x 0))))
    (hz : z.asIdeal.comap ((algebraMap (T ⧸ b) _).comp (Ideal.Quotient.mk b)) =
      IsLocalRing.maximalIdeal T)
    [IsRegularLocalRing (LocalChart ρ z)]
    (p : PrimeSpectrum
      (MvPolynomial {i : Fin (r + 1) // i ≠ 0} (IsLocalRing.ResidueField T)))
    (hp : p.asIdeal.comap (residuePolynomialMap (T := T) r) =
      (PrimeSpectrum.comap ρ z).asIdeal.comap
        (Ideal.Quotient.mk (PermissibleCoordinateChart.relations x Finset.univ 0)))
    (χ : MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T) →+*
      Ideal.associatedGraded (IsLocalRing.maximalIdeal T))
    (hχ : IsParameterGradedMap x y χ)
    (hnu : nuStar (transformIdeal ρ z) = nuStar b) :
    ∃ (m : ℕ) (f : Fin m → T) (d : Fin m → ℕ)
      (φ : Fin m → MvPolynomial (Fin (r + 1)) (IsLocalRing.ResidueField T)),
      Monotone d ∧ (∀ i, 1 ≤ d i) ∧
      (∀ i, f i ∈ b ∧ f i ≠ 0 ∧ f i ∈ Ideal.span (Set.range x) ^ d i ∧
        f i ∈ IsLocalRing.maximalIdeal T ^ d i ∧
        f i ∉ IsLocalRing.maximalIdeal T ^ (d i + 1)) ∧
      (∀ i, InOrderSpace r p (d i) (φ i) ∧
        ∃ hi : f i ∈ IsLocalRing.maximalIdeal T ^ d i,
          χ (MvPolynomial.rename Sum.inl (φ i)) = initialForm T (d i) ⟨f i, hi⟩) ∧
      IsMinimalGeneratingFamily (adicInitialIdeal (IsLocalRing.maximalIdeal T) b)
        (fun i ↦ χ (MvPolynomial.rename Sum.inl (φ i))) := by
  sorry

end Hironaka
