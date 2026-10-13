/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.RingTheory.FormalGlueingH0
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.Paper.FormalGlueingCanonicalMaps
import Sheaf.RingTheory.FormalGlueingData

/-!
# Clearing denominators of a formal glueing chart section

Source: Stacks Project, More on Algebra, Lemmas 05EQ and 05EP in the proof of
Proposition 05ER (blueprint: lem-weil-pbc-formal-glueing-H0-chart-power-lift).
-/

@[expose] public section

universe u v w

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A chart section becomes the projection of a global compatible section after
multiplication by a power of the chart parameter.
Source: Stacks Project, More on Algebra, Remark 05EL, Lemmas 05EQ and 05EP,
and Proposition 05ER, second paragraph
(blueprint: lem-weil-pbc-formal-glueing-H0-chart-power-lift).

Proof:
Put `u = f i`. In the localization of the ambient product of the prime module and
all chart modules at `u`, form a tuple with prime coordinate
`(X.alpha i).symm (1 ⊗ x)` and chart coordinate `j` equal to
`X.alpha_overlap i j (x/1)`. The `i` chart coordinate is `x/1`: the cocycle with
all indices `i` implies that the invertible self-overlap is idempotent, hence the
identity, under the canonical identifications of repeated localization. The square
condition, evaluated on the prime coordinate, proves each localized prime/chart
compatibility equation. The cocycle, evaluated on `(x/1)/1`, proves each localized
chart/chart equation. Use the canonical swap and tensor comparison fraction
formulas of the canonical-maps lemma for these identifications.
There are only finitely many coordinates, so write the tuple with one common
power `u^a` as denominator, taking the maximum of the individual exponents. Its
numerator is a tuple in the original ambient product. Each of the finitely many
compatibility differences is zero after localization at `u`, so some power of `u`
kills it. Take one exponent `b` at least as large as all these exponents and multiply
the numerator by `u^b`. All the original compatibility equations now hold, so this
numerator defines an element `h` of `h0`. Its localized `i` coordinate is
`u^(a+b) • (x/1)`. The map from the `i` chart to its own localization is injective,
because `u` is already a unit on that chart. Consequently the original coordinate
of `h` is `u^(a+b) • x`; choose `n = a+b`.
This works also when `u = 0`: its chart is the zero module. The presence of `i`
excludes the empty index set; zero modules and zero rings cause no exception. -/
theorem h0_chart_power_lift {t : ℕ} (φ : R →+* S) (hflat : φ.Flat)
    (f : Fin t → R) (X : Data.{u, v, w} φ f) (i : Fin t)
    (x : piece (f i) (X.M i)) :
    ∃ (n : ℕ) (h : h0 φ f X), h.val.2 i = (f i) ^ n • x := by sorry

end FormalGlueing
