/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import WeilConjectures.Blowup.Affine.Principalization

/-!
# Regularity and coordinate intersections on a permissible blowup chart

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, Lemma 4.2.9,
printed p. 121, and Remark 4.2.2(i), printed p. 118
(blueprint: lem-trf-permissible-coordinate-chart).

The auxiliary definitions are the displayed presentation and its coordinate equations.
Reduced unions are expressed by radical ideals. Strict transforms use the existing
scheme-theoretic closure construction, rather than topological closures.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PermissibleCoordinateChart

variable {R : Type u} [CommRing R] {d : ℕ}

/-- The coordinate centre ideal. Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def center (t : Fin d → R) (J : Finset (Fin d)) : Ideal R :=
  Ideal.span (t '' (J : Set (Fin d)))

/-- The chart relations `t_i - t_j u_i`. Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def relations (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    Ideal (MvPolynomial (↥(J.erase j)) R) :=
  Ideal.span (Set.range fun i : ↥(J.erase j) ↦
    MvPolynomial.C (t i) - MvPolynomial.C (t j) * MvPolynomial.X i)

/-- The displayed quotient presentation of the chart. Source: ILO VIII, Lemma 4.2.9,
p. 121 (blueprint: lem-trf-permissible-coordinate-chart). -/
abbrev Chart (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :=
  MvPolynomial (↥(J.erase j)) R ⧸ relations t J j

/-- The class of the ratio variable `u_i`. Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def ratio (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) (i : ↥(J.erase j)) :
    Chart t J j :=
  Ideal.Quotient.mk (relations t J j) (MvPolynomial.X i)

/-- The equation of a strict coordinate transform: `1` for `i=j`, `u_i` for
`i ∈ J \ {j}`, and `t_i` otherwise. Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def strictEquation (t : Fin d → R) (J : Finset (Fin d)) (j i : Fin d) :
    Chart t J j :=
  if i = j then 1 else
    if h : i ∈ J.erase j then ratio t J j ⟨i, h⟩ else algebraMap R _ (t i)

/-- `none` labels the exceptional equation; `some i` labels the strict equation.
Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def equation (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    Option (Fin d) → Chart t J j
  | none => algebraMap R _ (t j)
  | some i => strictEquation t J j i

/-- The exceptional hyperplane together with the strict transforms indexed by `I`.
Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def labels (I : Finset (Fin d)) (j : Fin d) : Finset (Option (Fin d)) :=
  insert none ((I.erase j).image some)

/-- The ideal of an intersection of the specified coordinate hyperplanes.
Source: ILO VIII, Lemma 4.2.9 and Remark 4.2.2(i), pp. 118, 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def intersection (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d)
    (S : Finset (Option (Fin d))) : Ideal (Chart t J j) :=
  Ideal.span (equation t J j '' (S : Set (Option (Fin d))))

/-- The ideal of the union of the specified coordinate hyperplanes.
Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def unionIdeal (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d)
    (S : Finset (Option (Fin d))) : Ideal (Chart t J j) :=
  ⨅ k ∈ S, Ideal.span {equation t J j k}

/-- The coordinate centre ideal sheaf on the affine spectrum.
Source: ILO VIII, Lemma 4.2.9, p. 121, affine interpretation
(blueprint: lem-trf-permissible-coordinate-chart). -/
def centerSheaf (t : Fin d → R) (J : Finset (Fin d)) :
    (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((center t J).map (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The closed immersion of a coordinate hyperplane in the base.
Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def hyperplane (a : R) : Spec (.of (R ⧸ (Ideal.span {a} : Ideal R))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a} : Ideal R)))

/-- The chart structure morphism. Source: ILO VIII, Lemma 4.2.9, p. 121
(blueprint: lem-trf-permissible-coordinate-chart). -/
def projection (t : Fin d → R) (J : Finset (Fin d)) (j : Fin d) :
    Spec (.of (Chart t J j)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Chart t J j)))

/-- Regularity, reduced boundary equations, regular intersections with their codimensions,
and scheme-theoretic strict transforms on the permissible chart.
Source: ILO VIII, Lemma 4.2.9, p. 121, and Remark 4.2.2(i), p. 118
(blueprint: lem-trf-permissible-coordinate-chart).

Proof plan:
1. Permute the regular parameters to put `j` first. The parameter regular-sequence
and regular-quotient theorem (`lem-weil-pbc-regular-local-generators-regular-sequence`)
and the chart presentation (`lem-trf-blowup-chart-regular-sequence-presentation`)
give the stated quotient. Modulo `t_j` it is the polynomial ring over the regular
parameter quotient, regular by `lem-trf-polynomial-ring-regular-base`. The chart generator
is a nonzerodivisor (`lemma-nagata-chart-generator-regular`). Away from it use
`lem-weil-pbc-regular-local-localization`; at primes containing it use
`lem-exc-regular-local-lift-regular-sequence-quotient`.
2. Substitute `t_i=t_j u_i`. The extended centre is `(t_j)` by
`lemma-nagata-chart-extended-ideal-principal`. Radical ideals give exactly the reduced
coordinate union, using `def-weil-pbc-scheme-reduction`.
3. At each prime the vanishing coordinate classes are independent in the cotangent
space. Away from `t_j` the ratio equations are associates of the original parameters.
Over `t_j=0`, the chart relations distinguish the independent vanishing ratios and outside
parameters. Extend these classes to a minimal generating set. The regular-sequence
parameter theorem and regular-local localization prove regularity of every intersection
and a dimension drop of one for each chosen equation.
4. The strict transform is the schematic closure off the centre, using
`def-nagata-strict-transform`. On this chart that open is `D(t_j)`. The `i=j` transform
is empty. For the other indices the off-centre equations are `u_i` or `t_i`.
By `lem-trf-chart-coordinate-nonzerodivisors`, `t_j` remains a nonzerodivisor on each
coordinate quotient, so its off-centre part is schematically dense. Thus the kernel ideal
of the strict-transform map is exactly the indicated hyperplane ideal.
5. These are standard charts of one blowup (`def-nagata-global-blowup`), and the
expressions agree on overlaps. The same calculation for `I` gives the reduced preimage
of `H ∪ M`; for empty `I`, only the exceptional equation remains.
-/
theorem permissible_coordinate_chart
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d r : ℕ) (t : Fin d → R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (hr : 1 ≤ r) (hrd : r ≤ d)
    (J I : Finset (Fin d)) (hJ : J.Nonempty)
    (hJB : (J ∩ Finset.univ.filter (fun i : Fin d ↦ i.val < r)).Nonempty)
    (hI : I ⊆ Finset.univ.filter (fun i : Fin d ↦ i.val < r))
    (j : Fin d) (hj : j ∈ J) :
    (∃ e : Chart t J j ≃ₐ[R] AffineBlowup.chartRing (center t J) (t j),
      ∀ i : ↥(J.erase j),
        (e (ratio t J j i) : Localization.Away (t j)) =
          AffineBlowup.chartFraction (t j) 1 (t i)) ∧
    IsRegularRing (Chart t J j) ∧
    (Ideal.span {algebraMap R (Chart t J j)
      (∏ i ∈ Finset.univ.filter (fun i : Fin d ↦ i.val < r), t i)}).radical =
        unionIdeal t J j (labels (Finset.univ.filter (fun i : Fin d ↦ i.val < r)) j) ∧
    (∀ p : PrimeSpectrum (Chart t J j),
      ∃ s : List (Localization.AtPrime p.asIdeal),
        IsLocalRing.IsRegularSystemOfParameters s ∧
        ∃ f : {k : Option (Fin d) //
            k ∈ labels (Finset.univ.filter (fun i : Fin d ↦ i.val < r)) j ∧
              equation t J j k ∈ p.asIdeal} → Fin s.length,
          Function.Injective f ∧
          ∀ k, s.get (f k) = algebraMap (Chart t J j) (Localization.AtPrime p.asIdeal)
            (equation t J j k)) ∧
    (∀ S : Finset (Option (Fin d)),
      S ⊆ labels (Finset.univ.filter (fun i : Fin d ↦ i.val < r)) j →
        (Subsingleton (Chart t J j ⧸ intersection t J j S) ∨
          IsRegularRing (Chart t J j ⧸ intersection t J j S)) ∧
        ∀ p : PrimeSpectrum (Chart t J j), intersection t J j S ≤ p.asIdeal →
          ringKrullDim (Localization.AtPrime p.asIdeal) =
            ringKrullDim (Localization.AtPrime p.asIdeal ⧸
              (intersection t J j S).map
                (algebraMap (Chart t J j) (Localization.AtPrime p.asIdeal))) +
                  (S.card : WithBot ℕ∞)) ∧
    (((Ideal.span {∏ i ∈ I, t i} ⊓ center t J).map
      (algebraMap R (Chart t J j))).radical =
        unionIdeal t J j (labels I j)) ∧
    (∀ i ∈ I,
      (strictTransformMap (hyperplane (t i)) (projection t J j)
        (centerSheaf t J).support.compl).ker =
          (hyperplane (strictEquation t J j i)).ker) := by
  sorry

end AlgebraicGeometry.PermissibleCoordinateChart
