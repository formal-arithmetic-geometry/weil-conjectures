import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.MvPolynomial.Basic
import Sheaf.RingTheory.IsRegularSystemOfParameters
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Blowup.Affine.Principalization

/-!
# Nonzerodivisors in regular coordinate charts

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VIII, Lemma 4.2.9,
printed p. 121 (algebraic check from Stacks Tag 0BIQ)
(blueprint: lem-trf-chart-coordinate-nonzerodivisors).
-/

universe u

open scoped BigOperators
open MvPolynomial

/-- The relation for the `i`-th coordinate in the `j`-chart. -/
noncomputable def traceChartRelation {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) :
    MvPolynomial (J.erase j) R :=
  C (t i.1) - C (t j) * X i

/-- The ideal of relations defining the `j`-chart. -/
noncomputable def traceChartIdeal {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    Ideal (MvPolynomial (J.erase j) R) :=
  Ideal.span (Set.range (traceChartRelation t J j))

/-- The affine coordinate chart ring in the `j`-chart. -/
noncomputable abbrev traceChartRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) : Type u :=
  MvPolynomial (J.erase j) R ⧸ traceChartIdeal t J j

noncomputable instance traceChartRing.commRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    CommRing (traceChartRing t J j) := inferInstance

/-- The image of the `i`-th polynomial coordinate in a chart ring. -/
noncomputable def traceChartCoordinate {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) (hi : i ∈ J.erase j) :
    traceChartRing t J j :=
  Ideal.Quotient.mk _ (X (⟨i, hi⟩ : J.erase j))

/-- Quotient of a chart ring by one coordinate. -/
noncomputable abbrev traceChartCoordinateQuotient {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) (hi : i ∈ J.erase j) : Type u :=
  traceChartRing t J j ⧸
    Ideal.span ({traceChartCoordinate t J j i hi} : Set (traceChartRing t J j))

noncomputable instance traceChartCoordinateQuotient.commRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) (hi : i ∈ J.erase j) :
    CommRing (traceChartCoordinateQuotient t J j i hi) := inferInstance

/-- Quotient of a chart ring by one coefficient parameter. -/
noncomputable abbrev traceChartParameterQuotient {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j k : Fin d) : Type u :=
  traceChartRing t J j ⧸ Ideal.span ({algebraMap R (traceChartRing t J j) (t k)} :
    Set (traceChartRing t J j))

noncomputable instance traceChartParameterQuotient.commRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j k : Fin d) :
    CommRing (traceChartParameterQuotient t J j k) := inferInstance

/--
In a regular local ring, multiplication by the chart parameter is injective after
quotienting by any other chart coordinate or by a parameter outside the center.
Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VIII, Lemma 4.2.9,
printed p. 121; the two quotient computations use the regular-system and chart
presentation lemmas recorded in the node's proof dependencies.
(blueprint: lem-trf-chart-coordinate-nonzerodivisors)
-/
theorem traceChartCoordinateNonzerodivisors {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {d : ℕ} (t : Fin d → R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (J : Finset (Fin d)) (hJ : J.Nonempty) (j : Fin d) (hj : j ∈ J) :
    (∀ (i : Fin d) (hi : i ∈ J.erase j),
      Function.Injective (fun x : traceChartCoordinateQuotient t J j i hi =>
        Ideal.Quotient.mk _ (algebraMap R (traceChartRing t J j) (t j)) * x)) ∧
    (∀ k : Fin d, k ∉ J →
      Function.Injective (fun x : traceChartParameterQuotient t J j k =>
        Ideal.Quotient.mk _ (algebraMap R (traceChartRing t J j) (t j)) * x)) := by
  sorry
