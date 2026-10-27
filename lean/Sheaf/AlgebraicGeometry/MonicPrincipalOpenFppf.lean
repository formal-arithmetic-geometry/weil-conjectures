/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# Monic principal opens of the affine line are fppf covers

Source: Stacks Project, Tag 00FB, lemma-affineline-open and its coefficient image formula;
Tags 08JZ, 00HT, 01U5 and 01TP for localization, flatness and finite presentation.
(blueprint: lem-sfb-monic-principal-open-fppf)
-/

@[expose] public section

universe u

open CategoryTheory Polynomial

namespace AlgebraicGeometry

/-- The canonical projection `Spec A[T,Y]/(P(T)Y - 1) → Spec A`. Here `AdjoinRoot` is
literally the quotient of the polynomial ring in `Y` over `A[T]` by the displayed relation,
and the ring map is the composite of the two coefficient inclusions and the quotient map.
This is the principal open `D(P)` of the affine line, as in Stacks Project, Tags 00FB and
08JZ. No monicity is required to construct the map.
(blueprint: lem-sfb-monic-principal-open-fppf) -/
noncomputable def polynomialPrincipalOpenProjection {A : Type u} [CommRing A] (P : Polynomial A) :
    Spec (CommRingCat.of (AdjoinRoot (Polynomial.C P * Polynomial.X - 1))) ⟶
      Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom
    ((AdjoinRoot.of (Polynomial.C P * Polynomial.X - 1)).comp Polynomial.C))

/-- A monic principal open of the affine line is flat, locally of finite presentation, and
surjective over the base: hence it is an fppf cover. There is no positive-degree or nonzero-ring
assumption. Source: Stacks Project, Tag 00FB, lemma-affineline-open, proof; Tags 08JZ, 00HT,
01U5 and 01TP. (blueprint: lem-sfb-monic-principal-open-fppf)

Proof:
1. Put `B = A[T]`. By lem-weil-pbc-localization-away-polynomial-quotient (Tag 08JZ),
   `B[Y]/(P Y - 1)` identifies canonically as a `B`-algebra with `B[1/P]`, compatibly
   with the maps from `A`. Thus this projection factors through `Spec B`.
2. The polynomial projection is flat by lem-nagata-polynomial-projection-flat. The
   localization is flat by lem-weil-pbc-localization-flat, even if the multiplicative
   set contains zero. Apply lem-weil-pbc-flat-ring-map-iff-flat-affine and
   lem-pc-flat-compose to obtain flatness of the composite.
3. The displayed algebra has two generators and one relation over `A`, so is finitely
   presented. Using the whole source and target as affine neighbourhoods gives
   def-sbc-locally-finite-presentation at every point.
4. By lem-weil-pbc-spec-localization-away-basic-open, the localization has image `D(P)`
   in `Spec B`. By lem-sfb-polynomial-basic-open-image-coefficients (Tag 00FB), its
   image in `Spec A` consists of primes avoiding some coefficient of `P`. Monicity
   supplies the coefficient `1`, which no prime contains. The composite is surjective.
   For degree zero, `P = 1` and the quotient is `A[T]`. For the zero ring both spectra
   are empty, so surjectivity is vacuous. -/
theorem polynomialPrincipalOpenProjection_fppf {A : Type u} [CommRing A]
    (P : Polynomial A) (hP : P.Monic) :
    Flat (polynomialPrincipalOpenProjection P) ∧
      LocallyOfFinitePresentation (polynomialPrincipalOpenProjection P) ∧
      Surjective (polynomialPrincipalOpenProjection P) := by
  sorry

end AlgebraicGeometry
