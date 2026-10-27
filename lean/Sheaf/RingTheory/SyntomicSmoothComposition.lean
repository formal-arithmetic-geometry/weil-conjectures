/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.FiberDimension
import WeilConjectures.RingTheory.PolynomialQuotientDimensionLowerBound
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Composition of syntomic ring maps and smooth inputs

Source: Stacks Project, Algebra, Tags 00SZ (1), 00TA and 00U9, with
Definition 00SL (blueprint: lem-sfb-syntomic-smooth-composition).

Syntomicity is written out using the recorded flatness, finite-presentation and local
complete-intersection predicates. `Ideal.Fiber` writes the residue field on the left;
tensor symmetry identifies this with the fibre in the source. In the etale clause,
canonical `ULift` copies put rings from independent universes into one scheme universe.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Syntomic maps compose. Source: Stacks Project, Algebra, Tag 00SZ (1).
(blueprint: lem-sfb-syntomic-smooth-composition).

Proof, following the first four steps of the node:
1. Compose two relative global complete intersection presentations by lifting the second
set of equations to the first polynomial ring. After residue-field base change
(lem-weil-pbc-relative-global-complete-intersection-base-change), let the successive
nonzero fibres be U and V. Their dimensions are n-c and m-d. Identify topological
fibres with spectra of tensor fibres using lem-weil-pbc-fibre-spec-homeomorphism.
A prime of V exists by lem-weil-pbc-proper-ideal-contained-in-maximal; hence n >= c
and m >= d. U is Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
Apply lem-zl-source-dimension-fibre-bound for the upper bound n-c+m-d, and
lem-weil-pbc-polynomial-quotient-dimension-lower-bound for the opposite bound.
Thus the combined presentation is relative global complete intersection; zero fibres
impose no dimension condition.
2. At q in Spec T, contract to s in Spec S. Use the two lci fibre covers and
lem-weil-pbc-flat-map-local-criterion to apply
lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection twice.
This gives g outside s and h outside q with relative complete intersection charts
R -> S_g and S -> T_h. Finite presentation supplies the initial localization at 1.
3. Base change the second chart along S -> S_g. The localization base-change and
localization-of-localization lemmas identify its target with T_a for a = image(g)*h.
Then a is outside q, and step 1 gives a relative complete intersection R -> T_a.
4. These D(a) cover Spec T. By lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact,
choose a finite subcover whose elements generate 1. Apply
lem-trf-relative-ci-principal-cover-syntomic-gluing to obtain flatness, finite
presentation and lci fibres. For T = 0, use its allowed empty cover and 0 = 1.
The scalar tower specifies precisely the composite map, without a new hypothesis
on the given two ring maps. -/
theorem syntomic_comp
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.Flat R S] [FinitePresentation R S]
    [Module.Flat S T] [FinitePresentation S T]
    (hRS : ∀ p : PrimeSpectrum R,
      IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S))
    (hST : ∀ p : PrimeSpectrum S,
      IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber T)) :
    ∃ (_ : FinitePresentation R T), Module.Flat R T ∧
      ∀ p : PrimeSpectrum R,
        IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber T) := by
  sorry

/-- Every smooth ring map is syntomic. Source: Stacks Project, Algebra, Tag 00TA.
(blueprint: lem-sfb-syntomic-smooth-composition).

Proof, following steps 5 and 6 of the node:
5. A standard smooth presentation with n variables and c equations remains standard
smooth on each fibre by lem-weil-pbc-standard-smooth-base-change. Its dimension
at every point is n-c by lem-weil-pbc-standard-smooth-over-field-dimension-at-points.
A nonzero fibre has a prime by lem-weil-pbc-proper-ideal-contained-in-maximal, so
lem-weil-pbc-dimension-supremum-local-dimensions makes its global dimension n-c.
Thus the presentation is relative global complete intersection. Zero fibres are allowed.
6. The lemma lem-weil-pbc-smooth-ring-map-locally-standard-smooth gives such a chart
at every prime. Quasi-compactness and the basic-open/unit-ideal criterion select a
finite cover. Apply lem-trf-relative-ci-principal-cover-syntomic-gluing, obtaining
all three syntomic properties. The empty spectrum is handled by the empty cover. -/
theorem syntomic_of_smooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Smooth R S] :
    Module.Flat R S ∧ FinitePresentation R S ∧
      ∀ p : PrimeSpectrum R,
        IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  sorry

/-- A ring map whose affine spectrum morphism is etale is syntomic.
Source: Stacks Project, Algebra, Tags 00U9 and 00TA, using the affine criterion 02GJ.
(blueprint: lem-sfb-syntomic-smooth-composition).

Proof, step 7 of the node: the canonical ring equivalences from the two ULift copies
identify the displayed map with R -> S. The lemma
lem-weil-pbc-etale-ring-map-iff-etale-affine gives finite presentation, zero H1 of
the naive cotangent complex, and zero Kahler differentials. The zero module is finite
projective (free on the empty basis), so these are the smoothness conditions.
Apply the smooth clause above (steps 5 and 6) to obtain the three syntomic properties.
The lifts only permit independently sized rings to inhabit one scheme category;
no algebra structure or scalar map is chosen. -/
theorem syntomic_of_etale_spec
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (h : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom ((algebraMap R S).ulift.{v, u})))) :
    ∃ (_ : FinitePresentation R S), Module.Flat R S ∧
      ∀ p : PrimeSpectrum R,
        IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  sorry

end Algebra
