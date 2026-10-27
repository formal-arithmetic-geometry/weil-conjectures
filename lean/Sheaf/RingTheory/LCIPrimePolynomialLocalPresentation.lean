module

public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence

/-!
# Polynomial local presentations of local complete intersections

Source: Stacks Project, Algebra, Tags 00S9, 00SC (last paragraph), and 00SG,
(3) implies (1) (blueprint: lem-trf-lci-prime-polynomial-local-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- An LCI algebra has, near each prime, a global complete-intersection polynomial
presentation whose equations become a regular sequence in a regular local polynomial ring.
The final algebra equivalence is the canonical one: `ι` is the unique map `S_h → S_q`
extending `S → S_q`, and the final equality characterizes the equivalence on polynomial
numerators. Since the denominators are units, it also characterizes its value on every
fraction. In particular, the intermediate identification of local rings sends
`(a/h^i)/(b/h^j)` to `a*h^j/(h^i*b)`.

Source: Stacks Project, Algebra, Tags 00S9, 00SC (last paragraph), and 00SG,
(3) implies (1) (blueprint: lem-trf-lci-prime-polynomial-local-presentation).

Proof:
1. By `def-weil-pbc-complete-intersection-over-field`, choose a principal open of the
LCI cover containing `q`, with defining element `h ∉ q`. The global complete-intersection
presentation of `S_h` supplies `m`, `c`, `f`, and `θ`, with dimension `m - c`.
2. By `lem-weil-pbc-localization-prime-residue-field-iso`, extension of `q` to `S_h`
is a proper prime and contracts to `q`: powers of `h` avoid `q`. Thus `S_h` is nonzero.
Pull this prime back along `θ` and the quotient map to obtain `b`, containing all `f i`.
3. By `lem-weil-pbc-polynomial-ring-field-regular-ring`, the polynomial localization at
`b` is regular local. It is essentially of finite type by
`def-weil-pbc-essentially-finite-type-algebra`, since the polynomial algebra is generated
by its finitely many variables (`def-weil-pbc-mv-polynomial-ring` and
`def-weil-pbc-finite-type-algebra`).
4. Transport dimension along `θ` and apply
`lem-weil-pbc-global-complete-intersection-local-regular-sequence` to get regularity of
`f i / 1` in the localization at `b`. All these elements lie in its maximal ideal,
since `b` contains the equations (`def-weil-pbc-localization-at-prime`).
5. Apply `lem-weil-pbc-localization-at-prime-of-quotient`, transport along `θ`, and apply
`lem-weil-pbc-localization-prime-residue-field-iso` to identify the resulting local ring
with `S_q`. The first two maps send `r/t` to `θ(r̄)/θ(t̄)`; the last map sends
`(a/h^i)/(b/h^j)` to `a*h^j/(h^i*b)`. Its denominator is allowed because `h,b ∉ q`.
These formulas preserve the fraction relation, and the inverse composites cancel powers
of the unit `h`. They fix `k` and give precisely the displayed normalization. The quotient
ideal is the span of the localized equations by localization of finite linear combinations.
The argument includes empty sequences and zero variables; the zero ring has no prime. -/
theorem exists_prime_polynomial_local_presentation
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (hlci : IsLocalCompleteIntersection k S)
    (q : Ideal S) [q.IsPrime] :
    ∃ (h : S), h ∉ q ∧
      ∃ (m c : ℕ) (f : Fin c → MvPolynomial (Fin m) k)
        (θ : (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k]
          Localization.Away h),
        c ≤ m ∧
        topologicalKrullDim (PrimeSpectrum (Localization.Away h)) =
          (↑(m - c) : WithBot ℕ∞) ∧
        ∃ (b : PrimeSpectrum (MvPolynomial (Fin m) k)),
          b.asIdeal = (q.map (algebraMap S (Localization.Away h))).comap
            (θ.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range f)))) ∧
          IsRegularLocalRing (Localization.AtPrime b.asIdeal) ∧
          Algebra.EssFiniteType k (Localization.AtPrime b.asIdeal) ∧
          RingTheory.Sequence.IsRegular (Localization.AtPrime b.asIdeal)
            ((List.ofFn f).map
              (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime b.asIdeal))) ∧
          (∀ i : Fin c,
            algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime b.asIdeal) (f i) ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime b.asIdeal)) ∧
          ∃ (ι : Localization.Away h →ₐ[k] Localization.AtPrime q)
            (e : (Localization.AtPrime b.asIdeal ⧸ Ideal.span
              (Set.range (fun i : Fin c ↦
                algebraMap (MvPolynomial (Fin m) k)
                  (Localization.AtPrime b.asIdeal) (f i)))) ≃ₐ[k] Localization.AtPrime q),
            (∀ s : S, ι (algebraMap S (Localization.Away h) s) =
              algebraMap S (Localization.AtPrime q) s) ∧
            ∀ r : MvPolynomial (Fin m) k,
              e (Ideal.Quotient.mk _
                (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime b.asIdeal) r)) =
                ι (θ (Ideal.Quotient.mk (Ideal.span (Set.range f)) r)) := by
  sorry

end Algebra
