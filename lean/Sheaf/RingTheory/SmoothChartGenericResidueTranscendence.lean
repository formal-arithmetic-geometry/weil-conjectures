module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.RingTheory.FibrePrimesResidueFields
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Generic-component transcendence degree in a smooth local chart

Source: Stacks Project, Morphisms, Tag 02G1, and Algebra, Tag 00P1
(blueprint: lem-trf-smooth-chart-generic-residue-transcendence).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- The closed-fibre point dimension of a smooth chart is the sum of the local-ring
dimension and residue transcendence degree; it is also the generic-component
transcendence degree for every minimal component through the point.

Source: Stacks Project, Morphisms, Tag 02G1
(`lemma-smooth-omega-finite-locally-free`), and Algebra, Tag 00P1
(`lemma-dimension-at-a-point-finite-type-field`)
(blueprint: lem-trf-smooth-chart-generic-residue-transcendence).

Conventions: `m` names the maximal ideal of `A`, `B = Localization.AtPrime N`,
`K = m.ResidueField`, and `L = N.ResidueField`. For the generic component `Q`,
put `p = Q.comap (algebraMap A P)`, `E = p.ResidueField`, `H = Q.ResidueField`.
Mathlib supplies `IsFractionRing (A / p) E` and `IsFractionRing (P / Q) H`, so these
are models of exactly the fraction fields in the source. The field inclusion is
`Ideal.ResidueField.map p Q (algebraMap A P) rfl`. Fibre rings use Mathlib's tensor
order `E ⊗[A] P`, canonically the source's `P ⊗[A] E`. Both residue-field and final
fraction-field identifications fix the image of `P`. They therefore fix `A / p`
and its fractions, which is precisely compatibility with `E`.

Proof:
1. Smoothness gives finite presentation and hence finite type of the closed and
   generic fibre algebras. Use lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
   lem-weil-pbc-fibre-product-affine-spectra to identify their spectra with the
   scheme fibres.
2. lem-weil-pbc-fibre-ring-primes-residue-fields and
   lem-weil-pbc-fibre-ring-local-ring-iso identify the closed-fibre point's residue
   field with `L` and its local ring with `B / mB`.
   lem-weil-pbc-dimension-at-point-local-ring-trdeg gives finite natural witnesses
   `r,s,t` and `r = s + t`.
3. Apply lem-weil-pbc-localization-quotient-by-prime to the complement of a prime:
   its residue field is the fraction field of its prime quotient. The injection
   `A / p → P / Q` extends uniquely to the specified field inclusion `E → H`.
4. The order-preserving correspondence of
   lem-weil-pbc-fibre-ring-primes-residue-fields makes the generic-fibre prime
   minimal. By lem-weil-pbc-primes-of-localization its local ring has just one
   prime, and hence dimension zero, even when the rings are nonreduced.
5. sbc-lem-smooth-relative-dimension-locally-constant gives a neighbourhood of `N`
   with constant fibre point dimension. Since `Q ≤ N`, every basic neighbourhood
   of `N` contains `Q`. Thus the dimension at the generic-fibre prime equals `r`.
6. Apply lem-weil-pbc-dimension-at-point-local-ring-trdeg to that generic-fibre
   prime. Its local-ring dimension is zero and its residue field is `H`, so its
   point dimension equals `trdeg_E H = r`.
7. lem-weil-pbc-primes-of-localization and
   lem-weil-pbc-localization-quotient-by-prime identify `B / QB` with the
   localization of the domain `P / Q` at the images of `P \ N`. Its fraction field
   is the fraction field of `P / Q`: the maps on fractions send `a/b` to `a/b`.
   They fix `P / Q` and therefore `A / p` and its fractions, giving compatibility
   with `E` as well as the displayed compatibility on `P`. -/
theorem smooth_chart_generic_residue_transcendence
    {A : Type u} {P : Type v} [CommRing A] [CommRing P]
    [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A P] [Smooth A P]
    (m : Ideal A) [m.IsMaximal] (hm : m = IsLocalRing.maximalIdeal A)
    (N : Ideal P) [N.IsPrime] (hN : m = N.comap (algebraMap A P)) :
    ∃ (n : PrimeSpectrum (m.Fiber P)) (r s t : ℕ),
      n.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = N ∧
      topologicalKrullDimAt
        (n : AlgebraicGeometry.Spec (CommRingCat.of (m.Fiber P))) =
          (r : WithBot ℕ∞) ∧
      ringKrullDim (Localization.AtPrime N ⧸
        m.map (algebraMap A (Localization.AtPrime N))) = (s : WithBot ℕ∞) ∧
      @Algebra.trdeg m.ResidueField N.ResidueField _ _
        (Ideal.ResidueField.map m N (algebraMap A P) hN).toAlgebra =
          (t : Cardinal.{v}) ∧
      r = s + t ∧
      ∀ (Q : PrimeSpectrum P), Q.asIdeal ∈ minimalPrimes P → Q.asIdeal ≤ N →
        Q.asIdeal.comap (algebraMap A P) ∈ minimalPrimes A →
        ∃ q : PrimeSpectrum ((Q.asIdeal.comap (algebraMap A P)).Fiber P),
          q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = Q.asIdeal ∧
          q.asIdeal ∈ minimalPrimes ((Q.asIdeal.comap (algebraMap A P)).Fiber P) ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0 ∧
          (∃ θ : q.asIdeal.ResidueField ≃+* Q.asIdeal.ResidueField,
            ∀ x : P,
              θ (algebraMap _ q.asIdeal.ResidueField
                (Algebra.TensorProduct.includeRight (R := A)
                  (A := (Q.asIdeal.comap (algebraMap A P)).ResidueField) x)) =
                  algebraMap P Q.asIdeal.ResidueField x) ∧
          @Algebra.trdeg (Q.asIdeal.comap (algebraMap A P)).ResidueField
            Q.asIdeal.ResidueField _ _
            (Ideal.ResidueField.map (Q.asIdeal.comap (algebraMap A P)) Q.asIdeal
              (algebraMap A P) rfl).toAlgebra = (r : Cardinal.{v}) ∧
          topologicalKrullDimAt
            (q : AlgebraicGeometry.Spec
              (CommRingCat.of ((Q.asIdeal.comap (algebraMap A P)).Fiber P))) =
                (r : WithBot ℕ∞) ∧
          ∃ e : Q.asIdeal.ResidueField ≃+*
              FractionRing (Localization.AtPrime N ⧸
                Q.asIdeal.map (algebraMap P (Localization.AtPrime N))),
            ∀ x : P,
              e (algebraMap P Q.asIdeal.ResidueField x) =
                algebraMap _ (FractionRing (Localization.AtPrime N ⧸
                  Q.asIdeal.map (algebraMap P (Localization.AtPrime N))))
                    (Ideal.Quotient.mk
                      (Q.asIdeal.map (algebraMap P (Localization.AtPrime N)))
                      (algebraMap P (Localization.AtPrime N) x)) := by
  sorry

end Algebra
