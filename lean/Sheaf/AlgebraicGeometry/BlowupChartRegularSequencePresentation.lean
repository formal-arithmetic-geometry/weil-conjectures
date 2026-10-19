/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q91 stage 2
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular

/-!
# Polynomial presentation of a regular-sequence blowup chart

Source: Stacks Project, More on Algebra, Lemma Tag 0BIQ (blueprint:
`lem-trf-blowup-chart-regular-sequence-presentation`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- For a regular sequence, the affine blowup chart has the standard polynomial quotient
presentation.  The quotient variables record the ratios `a i.succ / a 0`.

Source: Stacks Project, More on Algebra, Lemma Tag 0BIQ.
(blueprint: lem-trf-blowup-chart-regular-sequence-presentation)

Proof, following Tag 0BIQ and the five steps of the node:
1. Put `S = R[y_i]`, `f = (a, a_i)`, `q_i = a*y_i-a_i`, and `J = (q_i)`.
   Membership in a prefix ideal extended to `S` is coefficientwise. Thus successive
   injectivity and the nonzero final quotient persist, so `f` is regular over `S`.
2. Apply `lem-weil-pbc-regular-sequence-koszul-regular` to get `H_1(K(S,f)) = 0`.
   By the explicit differential of `def-weil-pbc-koszul-complex`, every syzygy is a
   sum of `b_ij*(f_i*e_j-f_j*e_i)` for `i < j`.
3. If `a*h = sum c_i*q_i`, then `(h-sum c_i*y_i, c_i)` is a syzygy. Apply the
   linear form taking `e_0` to `1` and `e_i` to `y_i`: its value is `h`, and its
   values on the boundaries are `q_j` or `y_i*q_j-y_j*q_i`, hence belong to `J`.
   Therefore `h` belongs to `J`; iteration gives absence of all `a`-power torsion.
4. Evaluation `y_i` at `a_i/a` kills `J` and surjects onto the subalgebra of
   `def-nagata-blowup-chart-ring`: for `x = r*a + sum r_i*a_i`, its generator
   `x/a` is `r + sum r_i*(a_i/a)`. For a polynomial `P`, choose `D` at least
   every total monomial degree. The relations give `a^D*P = c` modulo `J`, for
   a constant `c`. If `P` evaluates to zero, localization gives `a^N*c = 0`
   for some `N`, hence `a^(N+D)*P` belongs to `J`. Conversely every power-torsion
   class evaluates to zero, since `a` is invertible in the localization.
5. Steps 3 and 4 make evaluation bijective and hence an `R`-algebra equivalence.
   The images of the variables determine this equivalence uniquely. For `s = 0`
   the variable and relation families are empty; regularity of the sole element
   identifies its chart with `R`, so the one-element sequence is included.
-/
theorem blowupChartRegularSequencePresentation
    {R : Type u} [CommRing R] (s : ℕ) (a : Fin (s + 1) → R)
    (hreg : RingTheory.Sequence.IsRegular R (List.ofFn a)) :
    ∃ e :
        (MvPolynomial (Fin s) R ⧸
            Ideal.span (Set.range (fun i : Fin s ↦
              MvPolynomial.C (a 0) * MvPolynomial.X i - MvPolynomial.C (a i.succ)))) ≃ₐ[R]
          AlgebraicGeometry.AffineBlowup.chartRing
            (Ideal.span (Set.range a)) (a 0),
      ∀ i : Fin s,
        ((e (Ideal.Quotient.mk _ (MvPolynomial.X i)) :
            AlgebraicGeometry.AffineBlowup.chartRing
              (Ideal.span (Set.range a)) (a 0)) :
            Localization.Away (a 0)) =
          AlgebraicGeometry.AffineBlowup.chartFraction (a 0) 1 (a i.succ) := by
  sorry

end AlgebraicGeometry
