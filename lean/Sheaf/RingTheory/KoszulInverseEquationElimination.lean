module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.KoszulRegularSequence

import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Sheaf.RingTheory.KoszulSplitConormalCancellation

/-!
# Eliminating an inverse equation from local Koszul generators

Source: Stacks Project, More on Algebra, Tag 07D1 (lemma-lci-local), the local
subargument removing the inverse equation; Divisors, Tag 068Z(3), affine cancellation
(blueprint: lem-sfb-koszul-inverse-equation-elimination).

The one-variable ring is `MvPolynomial (Fin 1) A`, with variable `X 0`. Extension of
an ideal is `Ideal.map`, addition of ideals is `⊔`, and a finite tuple generates
`Ideal.span (Set.range ...)`. All localizations are the canonical `Localization.Away`.
The prime `q' = q B + (h z - 1)` is written out in the nonmembership hypothesis.
Its quotient is `(A/q)[1/h]`; its primality follows from `q.IsPrime` and `h ∉ q`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- Local Koszul-regular generators descend after eliminating `h z - 1`.
Source: Stacks Project, More on Algebra, Tag 07D1 (lemma-lci-local), final local
subargument, using Divisors, Tag 068Z(3)
(blueprint: lem-sfb-koszul-inverse-equation-elimination).

Proof:
1. Set `B = A[z]`, `t = h z - 1`, `R = B_v`, `L = J R`, and `K = t R`.
   If `t ∑ a_i z^i = 0`, coefficient comparison first gives `a_0 = 0`, then
   `a_i = h a_(i-1) = 0`. Thus multiplication by `t` is injective on `B`.
   If `t (p/v^m) = 0`, some `v^n t p = 0`, hence `v^n p = 0`; it remains
   injective on `R`. The one-term Koszul complex is `[R --t--> R]`, so `(t)`
   is Koszul-regular. The given tuple generates `L` and is Koszul-regular.
   Both ideals therefore satisfy local generation with localization element `1`.
   Also `K` is finitely generated and `R/L → K/KL`, `[a] ↦ [ta]`, is an
   isomorphism by injectivity of multiplication by `t`.
2. In `R[ε]/(ε²)`, substitute `z ↦ z(1+ε)`, fixing `A`. The image of `v` is
   `v + ε z v'`, whose inverse is `v⁻¹ - ε z v' v⁻²`, so this gives a map
   on `R`. Write it as `x ↦ x + ε δ(x)`. Multiplicativity gives the product
   rule, and `δ(t) = hz ≡ 1 mod L`. Thus `[x] ↦ [t δ(x)]` defines an
   `R/L`-linear map `ρ : L/L² → K/KL`: the product rule kills `L²` modulo
   `KL` and gives linearity. For `x = ta` it gives `ρ([ta]) = [ta]`.
   This retracts the inclusion-induced map `α : K/KL → L/L²`. The remaining
   exactness is `ker(L/L² → L/(K+L²)) = (K+L²)/L² = im α`.
3. The extended ideal `p = q' R` is prime and contains `L`, since its quotient
   is the nonzero domain `((A/q)_h)_v`. Apply
   `lem-sfb-koszul-split-conormal-cancellation`, namely
   `Ideal.koszulRegular_quotient_of_split_conormal`, to `K ≤ L` and `p/K`.
   Steps 1 and 2 supply its finite-generation, local-generation and splitting
   hypotheses. It gives `u ∈ C = R/K` outside `p/K` and a finite
   Koszul-regular tuple generating `(L/K) C_u`.
4. Evaluation `z ↦ h⁻¹` identifies `B/(t)` with `A_h`; the inverse sends
   `h⁻¹` to `z`, and both composites fix the generators. Consequently
   `C = (A_h)_w`, where `w = v(h⁻¹) = c/h^N` for some `c ∉ q`.
   Hence `C ≅ A_(hc)` with `p/K` extending `q` and `L/K = IC`. Write
   `u = a/(hc)^M`; nonmembership implies `a ∉ q`. Set `d = hca ∉ q`.
   Then `C_u ≅ A_d` as `A`-algebras. Transport the tuple from step 3 across
   this isomorphism. It generates `I A_d`, and the coefficientwise
   isomorphism of Koszul complexes identifies kernels and images, preserving
   all positive homology vanishing. This also allows the empty tuple.
-/
theorem koszulRegular_of_inverse_equation
    {A : Type u} [CommRing A] (I q : Ideal A) (hq : q.IsPrime) (hIq : I ≤ q)
    (h : A) (hh : h ∉ q) (v : MvPolynomial (Fin 1) A)
    (hv : v ∉ q.map MvPolynomial.C ⊔
      Ideal.span {MvPolynomial.C h * MvPolynomial.X 0 - 1})
    (e : ℕ) (b : Fin e → Localization.Away v)
    (hgen : Ideal.span (Set.range b) =
      (I.map MvPolynomial.C ⊔
        Ideal.span {MvPolynomial.C h * MvPolynomial.X 0 - 1}).map
          (algebraMap (MvPolynomial (Fin 1) A) (Localization.Away v)))
    (hreg : RingTheory.Sequence.IsKoszulRegular b) :
    ∃ d : A, d ∉ q ∧ ∃ (r : ℕ) (f : Fin r → Localization.Away d),
      Ideal.span (Set.range f) = I.map (algebraMap A (Localization.Away d)) ∧
        RingTheory.Sequence.IsKoszulRegular f := by
  sorry

end Ideal
