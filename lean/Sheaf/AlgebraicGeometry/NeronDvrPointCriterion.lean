/-
Copyright (c) 2026 The SHEAF project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.AlgebraicGeometry.FibreStalkQuotient

/-!
# Essentially smooth DVR point criterion for Néron lft-models

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §10.1, Proposition 2,
printed p. 290 (PDF p. 296) (blueprint: lem-sfb-neron-dvr-point-criterion).

The generic fibre is `(Over.pullback (Spec.map (algebraMap R K))).obj N`.
In the point condition we use the canonical identification
`G(Frac A) = Hom_R(Spec (Frac A), N)`, given by the pullback universal property
and the unique embedding `K → Frac A` extending the injective map `R → A`.
Thus restriction of points is literally precomposition with `Spec A ← Spec (Frac A)`.
The stalk isomorphism is required to commute with the given structural morphism to `Spec R`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The Néron mapping property is equivalent to extension of points over every essentially
smooth local injective extension of DVRs. No quasi-compactness of the model is assumed.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §10.1, Proposition 2 and proof,
printed p. 290 (PDF p. 296) (blueprint: lem-sfb-neron-dvr-point-criterion).

Proof:
1. A DVR is regular and normal: its only primes are zero and the maximal ideal
   (`lem-sc-dvr-dimension-one`, `def-weil-regular-scheme`,
   `lem-weil-pbc-regular-ring-normal`). Smooth schemes over it are regular and normal
   (`lem-weil-pbc-regular-ring-smooth-ascent`), reduced and locally Noetherian, with dense
   generic fibre (`lem-trf-smooth-reduced-dense-pullback`).
2. Every point of a smooth scheme has an integral affine neighbourhood: Noetherianity
   gives finitely many components, which normality makes disjoint and open
   (`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`,
   `lem-trf-normal-topologically-noetherian-components`). Affine stalks are localizations
   (`lem-weil-pbc-affine-open-stalk-localization`).
3. For the forward implication, let A be a test DVR and F its fraction field. A uniformizer
   of R maps to a nonzero nonunit of A. The DVR factorization shows that inverting it gives
   F (`lem-weil-pbc-dvr-unit-times-uniformizer-power`). Choose an affine smooth chart of N
   around the image of the given F-point; its algebra is finitely presented
   (`def-sbc-locally-finite-presentation`).
4. On an integral affine neighbourhood of the stalk point, invert finitely many
   denominators outside its prime to spread the generators and relations of this chart
   to the generic fibre of an open neighbourhood. Apply the mapping property there and
   restrict to Spec A. This extends the F-point.
5. Conversely, for a smooth X and a map of generic fibres, at every special-fibre point
   of ambient local dimension one the stalk is a DVR (`lem-sc-normal-dim1-dvr`). The map
   from R is local and injective: smoothness gives flatness (`lem-pc-smooth-flat`), hence
   multiplication by every nonzero element of R stays injective. Apply the point condition.
6. Spread each resulting stalk map to an open neighbourhood by the same finite-presentation
   denominator calculation. Its generic restriction agrees with the original generic map:
   they agree at the generic point and separatedness gives equality everywhere
   (`lem-sfb-relative-separated-dominant-ext`).
7. Glue these maps and the original generic map (`lem-weil-pbc-scheme-morphism-gluing`).
   On overlaps use the dense reduced generic fibre and separatedness again. The resulting
   open U contains every point of ambient codimension at most one; a dimension-zero local
   domain cannot receive a local injective map from R with nonzero nonunit uniformizer.
8. U is dense in each fibre. For the special fibre, at its component generic points the
   fibre local dimension is zero, so flatness and the local dimension formula give ambient
   dimension one (`lem-weil-pbc-flat-height-formula`, `lem-pc-smooth-flat`,
   `lem-sbc-scheme-fibre-stalk-quotient`). The generic fibre is already entirely in U.
9. Apply relative Weil extension (`lem-sfb-relative-group-weil-extension`) to extend U → N
   to X → N. Uniqueness follows from the dense reduced generic fibre and separatedness
   (`lem-sfb-relative-separated-dominant-ext`). All constructions are local followed by
   gluing, so require no quasi-compactness of N. Empty X gives singleton Hom sets. -/
theorem neron_mappingProperty_iff_dvr_points
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (N : Over (Spec (CommRingCat.of R))) [CommGrpObj N]
    [Smooth N.hom] [IsSeparated N.hom] [LocallyOfFiniteType N.hom]
    [QuasiCompact ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N).hom] :
    (∀ (X : Over (Spec (CommRingCat.of R))) (_ : Smooth X.hom),
      Function.Bijective (fun f : X ⟶ N ↦
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f)) ↔
    (∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      (φ : R →+* A) (_ : IsLocalHom φ) (_ : Function.Injective φ),
      (∃ (Y : Over (Spec (CommRingCat.of R))) (_ : Smooth Y.hom)
        (y : Y.left) (e : Y.left.presheaf.stalk y ≃+* A),
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.left.fromSpecStalk y ≫ Y.hom =
          Spec.map (CommRingCat.ofHom φ)) →
      Function.Surjective (fun f : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ N ↦
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))
          (rfl) :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫
            Spec.map (CommRingCat.ofHom φ)) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ f)) := by
  sorry

end AlgebraicGeometry
