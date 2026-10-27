module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.MvPolynomial.Basic
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Blowup.Affine.Principalization

/-!
# Nonzerodivisors in regular coordinate charts

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VIII, Lemma 4.2.9,
printed p. 121 (algebraic check from Stacks Tag 0BIQ)
(blueprint: lem-trf-chart-coordinate-nonzerodivisors).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators
open MvPolynomial

/-- The relation for the `i`-th coordinate in the `j`-chart.
Source: ILO, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable def traceChartRelation {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) :
    MvPolynomial (J.erase j) R :=
  C (t i.1) - C (t j) * X i

/-- The ideal of relations defining the `j`-chart.
Source: ILO, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable def traceChartIdeal {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    Ideal (MvPolynomial (J.erase j) R) :=
  Ideal.span (Set.range (traceChartRelation t J j))

/-- The affine coordinate chart ring in the `j`-chart.
Source: ILO, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable abbrev traceChartRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) : Type u :=
  MvPolynomial (J.erase j) R ⧸ traceChartIdeal t J j

/-- The inherited quotient ring structure.
Source: ILO VIII, Lemma 4.2.9, p. 121 (blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable instance traceChartRing.commRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    CommRing (traceChartRing t J j) := inferInstance

/-- The image of the `i`-th polynomial coordinate in a chart ring.
Source: ILO, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable def traceChartCoordinate {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) (hi : i ∈ J.erase j) :
    traceChartRing t J j :=
  Ideal.Quotient.mk _ (X (⟨i, hi⟩ : J.erase j))

/-- Quotient of a chart ring by one coordinate.
Source: ILO, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable abbrev traceChartCoordinateQuotient {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) (hi : i ∈ J.erase j) : Type u :=
  traceChartRing t J j ⧸
    Ideal.span ({traceChartCoordinate t J j i hi} : Set (traceChartRing t J j))

/-- The inherited quotient ring structure.
Source: ILO VIII, Lemma 4.2.9, p. 121 (blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable instance traceChartCoordinateQuotient.commRing {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) (hi : i ∈ J.erase j) :
    CommRing (traceChartCoordinateQuotient t J j i hi) := inferInstance

/-- Quotient of a chart ring by one coefficient parameter.
Source: ILO, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
noncomputable abbrev traceChartParameterQuotient {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (J : Finset (Fin d)) (j k : Fin d) : Type u :=
  traceChartRing t J j ⧸ Ideal.span ({algebraMap R (traceChartRing t J j) (t k)} :
    Set (traceChartRing t J j))

/-- The inherited quotient ring structure.
Source: ILO VIII, Lemma 4.2.9, p. 121 (blueprint: lem-trf-chart-coordinate-nonzerodivisors). -/
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

Proof:
1. For a ratio coordinate i, quotienting by u_i makes t_i zero. The coefficient and
   surviving-variable maps identify the result with the parameter chart over R/(t_i).
   Reorder parameters with t_i first, followed by t_j and the other centre parameters.
   The regular-generator theorem (lem-weil-pbc-regular-local-generators-regular-sequence)
   makes the remaining centre parameters a regular sequence over R/(t_i). Apply the
   chart-presentation theorem (lem-trf-blowup-chart-regular-sequence-presentation), then
   lemma-nagata-chart-generator-regular to get injectivity of the distinguished parameter.
   If the centre consists of j alone, there are no ratio coordinates to consider.
2. For k outside J, quotient coefficients by t_k instead, leaving all variables. Reorder
   with t_k first, then t_j and the remaining centre parameters. The same regular-generator,
   chart-presentation and chart-generator results apply over R/(t_k). This includes a
   singleton centre, when there are no variables and the quotient chart is R/(t_k).
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
