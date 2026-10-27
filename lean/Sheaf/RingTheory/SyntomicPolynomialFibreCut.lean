/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection
import Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.EquationCountLocalizeRelativeGlobalCompleteIntersection
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionPrincipalLocalization

/-!
# Cutting polynomial coordinates in a syntomic reduction

Source: Stacks Project, Smoothing Ring Maps, Tag 07M8 (proposition-lift-smooth),
proof of assertion (1), final claim, with Algebra Tags 00SY and 00ST.
(blueprint: lem-sfb-syntomic-polynomial-fibre-cut).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

namespace Algebra

/-- Killing lifts of polynomial coordinates preserves syntomicity near the closed reduction.

Source: Stacks Project, Smoothing Ring Maps, Tag 07M8 (proposition-lift-smooth),
proof of assertion (1), final claim; local charts use Algebra Tag 00SY and
appending equations uses Tag 00ST (3).
(blueprint: lem-sfb-syntomic-polynomial-fibre-cut).

The ring equivalence `θ` together with `hθ` is exactly an `R/I`-algebra equivalence:
compatibility is checked on representatives from `R`, which surjects onto `R/I`.
The equation on `a` says that it is 1 in `A/IA`, equivalently in `A₀` under the
induced isomorphism. Here `A` is written explicitly as `D / span(range t)`.

Proof:
1. Reduce the quotient by the `tᵢ` modulo `I`. Under `θ` this is the quotient of
`A₀[x₁,...,xᵣ]` by its variables, hence `A₀`. Appending polynomial lifts of the
`tᵢ` to any finite presentation of `D` shows that `A` is finitely presented.
2. At each prime `q` of `A` containing `IA`, pull back to `D` and then to `R`.
The flat-local-ring-maps lemma gives a flat local map. The local complete
intersection fibre supplies a principal global-complete-intersection neighbourhood.
Apply lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection to
obtain a relative global complete intersection chart `Dᵤ` at this prime.
3. Set `k = κ(p)` and `B = A₀ ⊗[R/I] k`. The reduction identification gives
`D ⊗[R] k = B[x]` and `A ⊗[R] k = B`, with the selected prime on the zero section.
Use fibre-ring-primes-bijection, relative-global-complete-intersection-base-change,
global-complete-intersection-equidimensional, localization-away-base-change,
spec-localization-away-basic-open and dimension-at-point-open-subspace to compute
its dimension in `B[x]` as `N-c`. The polynomial-zero-section-dimension lemma
then gives dimension `N-c-r` in `B`.
4. Append polynomial lifts of the `tᵢ` to the chart's `c` equations. The resulting
presentation of `Aᵤ` has `N` variables and `c+r` equations and the expected fibre
dimension at the selected prime. Apply
lem-weil-pbc-equation-count-localize-relative-global-complete-intersection to
obtain a relative global complete intersection neighbourhood.
5. Write its further localizing element as `b/u^e`. The double localization is
`A[1/(ub)]`, and `ub` misses `q`. Thus principal relative global complete
intersection charts cover `V(IA)`.
6. Let `J` be the ideal of all these chart elements. By
lem-weil-pbc-spec-zero-loci-disjoint-unit-ideal, `J + IA = A`. Choose `a ∈ J`
congruent to 1 modulo `IA` and a finite expression of `a` in the chart elements.
Their images generate the unit ideal of `Aₐ`. If `V(IA)` is empty, take `a = 0`.
7. By relative-global-complete-intersection-principal-localization, localizing
these charts further at `a` preserves their relative global complete intersection
presentations. Apply lem-trf-relative-ci-principal-cover-syntomic-gluing to this
finite principal cover of `Aₐ`. This gives flatness, finite presentation and local
complete intersection fibres. Empty covers, zero rings and `r = 0` are allowed. -/
theorem exists_syntomic_localization_of_polynomial_reduction
    {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]
    (I : Ideal R) [Module.Flat R D] [FinitePresentation R D]
    (hciD : ∀ p : PrimeSpectrum R,
      IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber D))
    (A₀ : Type w) [CommRing A₀] [Algebra (R ⧸ I) A₀]
    [Module.Flat (R ⧸ I) A₀] [FinitePresentation (R ⧸ I) A₀]
    (hci₀ : ∀ p : PrimeSpectrum (R ⧸ I),
      IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber A₀))
    (r : ℕ) (θ : (D ⧸ I.map (algebraMap R D)) ≃+* MvPolynomial (Fin r) A₀)
    (hθ : ∀ x : R, θ (Ideal.Quotient.mk (I.map (algebraMap R D)) (algebraMap R D x)) =
      MvPolynomial.C (algebraMap (R ⧸ I) A₀ (Ideal.Quotient.mk I x)))
    (t : Fin r → D)
    (ht : ∀ i : Fin r,
      θ (Ideal.Quotient.mk (I.map (algebraMap R D)) (t i)) = MvPolynomial.X i) :
    ∃ (a : D ⧸ Ideal.span (Set.range t))
      (_ : FinitePresentation R (Localization.Away a)),
      Ideal.Quotient.mk
          (I.map (algebraMap R (D ⧸ Ideal.span (Set.range t)))) a = 1 ∧
        Module.Flat R (Localization.Away a) ∧
        ∀ p : PrimeSpectrum R,
          IsLocalCompleteIntersection p.asIdeal.ResidueField
            (p.asIdeal.Fiber (Localization.Away a)) := by
  sorry

end Algebra
