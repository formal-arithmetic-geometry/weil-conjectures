/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.QuadraticFormalCurve
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

/-!
# Normalization of a quadratic formal plane curve

Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1),
Cases I and II, interchanging X and Y in Case II.
(blueprint: lem-sfb-quadratic-series-integral-closure)

The polynomial, equation, quotient rings and coordinate classes are publicly
re-exported from `WeilConjectures.RingTheory.QuadraticFormalCurve`. Their definitions and
names are unchanged.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

namespace QuadraticSeries

/-- Normalization of the nondegenerate quadratic formal curve by the substitution
x = zt, y = t. Source: Stacks 0C4A (lemma-2-branches-delta-1), Cases I and II,
with the coordinates interchanged in Case II.
(blueprint: lem-sfb-quadratic-series-integral-closure)

Proof plan from the node:
1. Divide the equation by a. The monic-quotient basis theorem
   (lem-weil-pbc-monic-quotient-free) gives the coefficient basis 1,z and
   z² = -(b/a)z-c/a, including injectivity of the coefficient field map.
2. Substitute each homogeneous part H_n at (z,1). Convolution proves multiplicativity;
   the quadratic equation maps to zero, so this factors through R.
3. If H_n(z,1)=0, divide H_n(Z,1) by the monic quadratic. For n<2 it vanishes;
   otherwise homogenizing the quotient gives H_n=qG_(n-2). Summing by degree gives
   ker(phi)=(q), hence the induced j is injective.
4. The constant coefficient is in F. Conversely the series with coefficients
   alpha_n+delta_n*z has preimage alpha_0 + sum alpha_n*Y^n + sum delta_n*X*Y^(n-1).
   Thus j(R)=F+tB, containing F[[t]] and tB.
5. If the quadratic has a root r, its other root s is distinct by the discriminant;
   interpolation identifies L with F×F. Otherwise the norm
   u²-(b/a)uv+(c/a)v² is nonzero for u+vz nonzero and gives an explicit inverse.
   Hence L is a field or a product of two fields, in every characteristic.
6. Apply lem-weil-pbc-power-series-normal-domain to each field factor. B is reduced,
   and the injection j makes R reduced.
7. Multiplication by t shifts coefficients, so t and y are regular. The ideal
   (zt,t)B is tB. The basis 1,z generates B over F[[t]], hence over R, and
   h=u+zv satisfies h²+((b/a)v-2u)h+(u²-(b/a)uv+(c/a)v²)=0 over R.
8. If s is regular in R and sb=0 in B, then tb lies in R, so t*b=0 and b=0.
   This embeds Q(R) into the product of the fraction fields of the factors of B.
   Every h in B lies in Q(R) as (th)/t, compatibly with j. Denominators regular
   in B are inverted there as well, since t*s is regular in R.
9. Project a monic equation for w in Q(R) to each factor. Normality from
   lem-weil-pbc-power-series-normal-domain puts each coordinate in that factor
   of B. Injectivity gives w in B; step 7 gives the reverse inclusion. All maps,
   ideal extensions and the regular parameter use the same substitution j.
-/
theorem integral_closure (F : Type u) [Field F] (a b c : F)
    (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) :
    ∃ j : CurveRing a b c →ₐ[F] PowerSeries (CoefficientAlgebra a b c),
      (∀ (H : MvPowerSeries (Fin 2) F) (n : ℕ),
        PowerSeries.coeff n (j (Ideal.Quotient.mk (Ideal.span {equation a b c}) H)) =
          ∑ i ∈ Finset.range (n + 1),
            algebraMap F (CoefficientAlgebra a b c)
              (MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 (n - i)) H) *
                AdjoinRoot.root (polynomial a b c) ^ i) ∧
      j (x a b c) = PowerSeries.C (AdjoinRoot.root (polynomial a b c)) * PowerSeries.X ∧
      j (y a b c) = PowerSeries.X ∧
      Function.Injective j ∧
      (∀ h : PowerSeries (CoefficientAlgebra a b c),
        (∃ r, j r = h) ↔
          ∃ d : F, ∃ g : PowerSeries (CoefficientAlgebra a b c),
            h = PowerSeries.C (algebraMap F (CoefficientAlgebra a b c) d) +
              PowerSeries.X * g) ∧
      IsReduced (CurveRing a b c) ∧
      @Module.Finite (CurveRing a b c) (PowerSeries (CoefficientAlgebra a b c)) _ _
        (@Algebra.toModule _ _ _ _ j.toRingHom.toAlgebra) ∧
      Ideal.map j.toRingHom (Ideal.span {x a b c, y a b c}) =
        Ideal.span {PowerSeries.X} ∧
      y a b c ∈ nonZeroDivisors (CurveRing a b c) ∧
      PowerSeries.X ∈ nonZeroDivisors (PowerSeries (CoefficientAlgebra a b c)) ∧
      ∃ k : PowerSeries (CoefficientAlgebra a b c) →+* FractionRing (CurveRing a b c),
        Function.Injective k ∧
        k.comp j.toRingHom = algebraMap (CurveRing a b c) (FractionRing (CurveRing a b c)) ∧
        (∀ w : FractionRing (CurveRing a b c),
          w ∈ integralClosure (CurveRing a b c) (FractionRing (CurveRing a b c)) ↔
            ∃ h : PowerSeries (CoefficientAlgebra a b c), k h = w) := by
  sorry

end QuadraticSeries
