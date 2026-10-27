module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Prime-local criterion for integrality of an element

Source: Stacks Project, Tag 034K, `lemma-integral-closure-stalks`
(blueprint: lem-sfb-integral-element-prime-local-criterion).

The localization of the algebra uses the image of the complement of the base prime,
so its denominators act through the given algebra map. No injectivity or nontriviality
assumptions are needed.
-/

@[expose] public section

universe u v

/-- An algebra element is integral over the base ring if and only if its image is
integral after localization at each prime of the base.

Source: Stacks Project, Tag 034K, `lemma-integral-closure-stalks`
(blueprint: lem-sfb-integral-element-prime-local-criterion).

Proof:
1. A monic equation remains monic after localization. If the base is the zero ring,
   so is the algebra, and the element satisfies the monic polynomial `X`.
2. For the converse, put `B = R[a]`, the actual subalgebra of `A`. At a prime `p`,
   write a monic local equation with coefficients `r_i / s_i`. Set `d = product s_i`
   and `d_i = product (s_j, j ≠ i)`. The element
   `c = d * a^n + sum (r_i * d_i * a^i)` of `B` vanishes in `A_p`. The localization
   equality criterion supplies `u` outside `p` with `u * c = 0` already in `B`.
   Set `f = u * d`, outside `p`. Both `u` and `d` become units in `R_f`; dividing
   gives a monic equation for `a/1` in `B_f`. This uses only the fraction equality
   criterion of def-weil-pbc-module-localization, not injectivity of any localization map.
3. Every element of `B_f` is a polynomial in `a/1` over `R_f`. By
   lem-sc-finite-generated-integral-subring, this single integral generator makes
   `B_f` finite over `R_f`.
4. These principal opens `D(f)` cover the base spectrum. By
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact there is a finite subcover,
   and its defining elements generate the unit ideal.
5. Apply lem-weil-pbc-module-finite-of-localization-span to the module `B` and
   this finite unit-ideal cover to obtain that `B` is finite over `R`.
6. By lem-weil-pbc-finite-algebra-is-integral, `a` satisfies a monic equation in
   `B`. The inclusion `B → A` carries it to the required equation in `A`.
-/
theorem isIntegral_iff_isIntegral_atPrime {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    IsIntegral R a ↔ ∀ (p : Ideal R) [p.IsPrime],
      IsIntegral (Localization.AtPrime p)
        (algebraMap A (Localization (Algebra.algebraMapSubmonoid A p.primeCompl)) a) := by
  sorry
