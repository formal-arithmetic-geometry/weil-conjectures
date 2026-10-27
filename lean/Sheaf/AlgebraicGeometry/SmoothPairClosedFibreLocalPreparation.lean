/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Closed-fibre local preparation for a smooth closed pair

Source: EGA IV4, Proposition 21.14.3(ii), final proof paragraph
(blueprint: lem-sfb-smooth-pair-closed-fibre-local-preparation).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A point of a closed pair admits a closed specialization in its smooth fibre,
with the actual local map, finite residue extension and canonical localization.

Source: EGA IV4, Proposition 21.14.3(ii), final proof paragraph.
(blueprint: lem-sfb-smooth-pair-closed-fibre-local-preparation)

Proof:
1. Convert affine smoothness to a smooth ring map using
   `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` and
   `def-weil-pbc-smooth-ring-map`. The total ring is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. The affine fibre is its residue
   field tensor product (`lem-weil-pbc-fibre-product-affine-spectra`), whose local
   rings are regular by `lem-weil-pbc-smooth-fibre-regular-local`.
2. The fibre is Jacobson (`lem-sc-lft-over-field-jacobson-space`). Choose a closed
   point in the closure of z, which stays in Z. Its residue field is finite by
   `lem-weil-pbc-zariski-lemma`; the fibre and total-space residue fields agree by
   `lem-sbc-scheme-fibre-stalk-quotient`.
3. Identify the actual stalks with prime localizations by
   `lem-weil-pbc-affine-open-stalk-localization`. They are Noetherian local rings
   by `lem-weil-pbc-localization-noetherian` and `def-weil-pbc-localization-at-prime`.
   The stalk map is local (`def-weil-flat-morphism`). Its formal smoothness from
   `lem-sfb-smooth-stalk-formally-smooth` gives the restricted lifting property
   `def-weil-pbc-formally-smooth-adic`.
4. The quotient by the extended base maximal ideal is the fibre stalk
   (`lem-sbc-scheme-fibre-stalk-quotient` and
   `lem-weil-pbc-affine-open-stalk-localization`). It is regular local, hence a
   domain (`lem-sc-regular-local-domain`), so that extended ideal is prime.
5. A point in Z cannot be a minimal fibre prime, by
   `lem-weil-pbc-spec-irreducible-components-minimal-primes`. Choose a strictly
   smaller minimal prime (`lem-weil-pbc-prime-contains-minimal-prime`); the strict
   chain survives in its local ring by
   `lem-weil-pbc-localization-prime-residue-field-iso`. Thus its fibre stalk has
   dimension at least one (`def-weil-pbc-krull-dimension-ring`).
6. Smoothness gives flatness (`lem-weil-pbc-smooth-ring-map-flat`). Apply
   `lem-weil-pbc-flat-height-formula` at both points using the affine stalk
   identifications. Since the base local dimension is finite by
   `lem-weil-pbc-noetherian-local-finite-krull-dimension`, the positive fibre
   dimension implies the strict dimension inequality at y.
7. Specialization gives containment of coordinate primes. Extend the prime of z
   to the stalk at y using `lem-weil-pbc-localization-prime-residue-field-iso`.
   It is the contraction of the maximal ideal at z along the specialization stalk map.
   The strictly smaller fibre prime from step 5 shows that it strictly contains
   the extended base maximal ideal. The canonical iterated localization
   `lem-weil-pbc-localize-localization-at-prime`, followed by
   `lem-weil-pbc-affine-open-stalk-localization`, identifies its localization
   with the stalk at z and sends every germ to its specialization image.
8. Away from the generic base point the base local dimension is at least one:
   the strict chain from zero to its nonzero prime survives localization by
   `lem-weil-pbc-localization-prime-residue-field-iso`. Steps 5 and 6 give total
   local dimension at least two. At the generic base point, the fibre stalk is
   the total stalk by `lem-sbc-scheme-fibre-stalk-quotient`, so use the generic
   codimension hypothesis. Transport this bound through step 7. -/
theorem smooth_pair_closed_fibre_local_preparation
    (A₀ B₀ : Type u) [CommRing A₀] [CommRing B₀]
    [IsNoetherianRing A₀] [IsDomain A₀] [IsIntegrallyClosed A₀]
    (g : Spec (CommRingCat.of B₀) ⟶ Spec (CommRingCat.of A₀)) [Smooth g]
    (Z : Set (Spec (CommRingCat.of B₀))) (hZ : IsClosed Z)
    (hcomponents : ∀ s : Spec (CommRingCat.of A₀),
      ∀ C ∈ irreducibleComponents (g.fiber s), ¬ C ⊆ (g.fiberι s) ⁻¹' Z)
    (η : Spec (CommRingCat.of A₀)) (hη : IsGenericPoint η Set.univ)
    (hgeneric : ∀ w : g.fiber η, g.fiberι η w ∈ Z →
      2 ≤ ringKrullDim ((g.fiber η).presheaf.stalk w))
    (z : Spec (CommRingCat.of B₀)) (hz : z ∈ Z) :
    ∃ y ∈ Z, ∃ hy : g y = g z, ∃ hzy : z ⤳ y,
      (g.fiberHomeo (g z)).symm ⟨y, hy⟩ ∈ closedPoints (g.fiber (g z)) ∧
      IsNoetherianRing ((Spec (CommRingCat.of A₀)).presheaf.stalk (g y)) ∧
      IsLocalRing ((Spec (CommRingCat.of A₀)).presheaf.stalk (g y)) ∧
      IsNoetherianRing ((Spec (CommRingCat.of B₀)).presheaf.stalk y) ∧
      IsLocalRing ((Spec (CommRingCat.of B₀)).presheaf.stalk y) ∧
      IsLocalHom (g.stalkMap y).hom ∧
      @Algebra.FormallySmoothAdic _ _ _ _ (g.stalkMap y).hom.toAlgebra
        (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of B₀)).presheaf.stalk y)) ∧
      (g.residueFieldMap y).hom.Finite ∧
      ringKrullDim ((Spec (CommRingCat.of A₀)).presheaf.stalk (g y)) <
        ringKrullDim ((Spec (CommRingCat.of B₀)).presheaf.stalk y) ∧
      ((IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A₀)).presheaf.stalk (g y))).map
        (g.stalkMap y).hom).IsPrime ∧
      ∃ q : PrimeSpectrum ((Spec (CommRingCat.of B₀)).presheaf.stalk y),
        q.asIdeal =
          (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of B₀)).presheaf.stalk z)).comap
            ((Spec (CommRingCat.of B₀)).presheaf.stalkSpecializes hzy).hom ∧
        (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A₀)).presheaf.stalk (g y))).map
          (g.stalkMap y).hom < q.asIdeal ∧
        ∃ e : Localization.AtPrime q.asIdeal ≃+*
            (Spec (CommRingCat.of B₀)).presheaf.stalk z,
          (∀ b : (Spec (CommRingCat.of B₀)).presheaf.stalk y,
            e (algebraMap _ (Localization.AtPrime q.asIdeal) b) =
              ((Spec (CommRingCat.of B₀)).presheaf.stalkSpecializes hzy).hom b) ∧
          2 ≤ ringKrullDim (Localization.AtPrime q.asIdeal) := by
  sorry

end AlgebraicGeometry
