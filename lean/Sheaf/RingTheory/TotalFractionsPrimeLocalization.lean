module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions

/-!
# Total fractions after localization at a prime

Source: Stacks Project, Tag 02LX, `lemma-total-ring-fractions-no-embedded-points`,
with the fraction construction of Tag 00CO; the prime-localization consequence is
(blueprint: lem-trf-total-fractions-prime-localization).
-/

@[expose] public section

universe u

namespace IsFractionRing

/-- Total fractions of a reduced Noetherian ring commute with prime localization,
as algebras over the localized ring, with the specified fraction formula.
Source: Stacks Project, Tag 02LX, `lemma-total-ring-fractions-no-embedded-points`,
and Tag 00CO, `definition-localization`.
(blueprint: lem-trf-total-fractions-prime-localization)

Proof: Write `T` for the nonzerodivisors of `A`, `S = A ∖ p`, `R = S⁻¹A`, and
`E = S⁻¹Q(A)`.
1. The image of `T` in `R` consists of nonzerodivisors: clear an `S` denominator
   from a zero product and cancel its `T` factor in `A`. The map
   `j : R → E`, `a/s ↦ (a/1)/(s/1)`, is well defined and injective by the same
   fraction equality criterion of `def-weil-pbc-module-localization` and
   `def-weil-pbc-localization-at-prime`.
2. Every element of `E` is `j(b) / j(t/1)` for `b : R` and `t ∈ T`, and `j(t/1)`
   is a unit; this follows directly by multiplying fractions.
3. Apply `reduced_noetherian_total_ring_fractions`
   (`lem-weil-pbc-reduced-noetherian-total-ring-fractions`) to express `Q(A)` as
   a finite product of fields. Choosing the reciprocal of each nonzero coordinate
   and zero at zero coordinates gives `q²v = q`. Localizing gives, for every
   `x : E`, an element `y : E` with `x²y = x`.
4. If `r` is a nonzerodivisor of `R`, then `j(r)` is a nonzerodivisor of `E`:
   use step 2 to clear a unit denominator, then injectivity of `j` and cancellation
   of `r` in `R`.
5. Apply step 3 to `z = j(r)`. The equation `z(zy - 1) = 0` and step 4 imply
   `zy = 1`. Thus `j` extends to `F : Q(R) → E`, sending `b/r` to `j(b)/j(r)`.
   Fraction equality and the sum and product rules make this a unital ring map.
6. Step 1 defines the reverse map `G : E → Q(R)` by
   `(a/t)/(s/1) ↦ (a/s)/(t/1)`. The fraction relations make it well defined;
   `G ∘ F` and `F ∘ G` are identities by step 2. The maps respect the canonical
   `R`-algebra structures, and taking `t = 1` gives the displayed formula. -/
theorem exists_totalFractionsPrimeLocalization_algEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (p : Ideal A) [p.IsPrime] :
    ∃ e : Localization (Algebra.algebraMapSubmonoid (FractionRing A) p.primeCompl)
        ≃ₐ[Localization.AtPrime p] FractionRing (Localization.AtPrime p),
      ∀ (a : A) (s : p.primeCompl),
        e (Localization.mk (algebraMap A (FractionRing A) a)
          ⟨algebraMap A (FractionRing A) s,
            Algebra.mem_algebraMapSubmonoid_of_mem s⟩) =
          algebraMap (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))
            (Localization.mk a s) := by
  sorry

end IsFractionRing
