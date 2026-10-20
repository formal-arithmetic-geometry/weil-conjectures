/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.OpenFlatLocus
import WeilConjectures.RingTheory.FlatFinitePresentationModel
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber

/-!
# A fibre-regular germ cuts out a flat hypersurface locally

Source: Stacks Project, More on Morphisms, Tag 056Y, `lemma-slice-given-element`,
forgetting the additional effective-Cartier-divisor assertion
(blueprint: lem-trf-fibre-regular-element-flat-hypersurface).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A germ in the maximal ideal which is regular on the fibre of a morphism locally
of finite presentation and flat at the point has an affine representative whose
principal closed subscheme contains that point and is flat and locally of finite
presentation over the base.

Source: Stacks Project, More on Morphisms, Tag 056Y, `lemma-slice-given-element`,
with its effective-Cartier-divisor conclusion omitted.
(blueprint: lem-trf-fibre-regular-element-flat-hypersurface).

Proof plan (the twelve steps of the DAG node):
1. By `def-sbc-locally-finite-presentation`, choose affine neighbourhoods of x and
   its image. Use `lem-weil-pbc-affine-open-stalk-localization` to represent the
   specified germ by a fraction. Restrict to its denominator's principal open,
   using `lem-weil-pbc-affine-open-section-vanishing-prime`. Localization preserves
   finite presentation by adjoining an inverse variable with one relation.
2. The flat stalk map and `lem-weil-pbc-flat-over-localization` put x in the flat
   locus of the coordinate algebra as its own module. Shrink using
   `lem-weil-pbc-openness-of-flatness` and
   `lem-weil-pbc-spec-localization-away-basic-open`. Identify the stalk maps and use
   `def-weil-flat-morphism` and `lem-weil-pbc-flat-morphism-affine-criterion` to obtain
   a flat finitely presented algebra over the affine base.
3. Apply `lem-weil-pbc-flat-finite-presentation-model` to obtain a flat finitely
   presented model over a finitely presented integer algebra.
4. Write the chosen section as a finite tensor sum and enlarge the model base by
   its finitely many coefficients. Track the section through tensor reassociation.
   `lem-weil-pbc-flat-module-base-change` and
   `lem-weil-pbc-finite-presentation-base-change-composition` preserve flatness and
   finite presentation, and the enlarged model now contains the chosen section.
5. By `lem-weil-pbc-finite-type-algebra-noetherian`, both model rings are Noetherian:
   first use the integer base, then the finite-type model algebra.
6. Contract the chosen primes to the model. Use `def-pc-scheme-fibre`,
   `lem-weil-pbc-fibre-product-affine-spectra`,
   `lem-weil-pbc-affine-open-stalk-localization`, and
   `lem-sbc-scheme-fibre-stalk-quotient` to identify the fibre stalks, preserving
   the chosen element under the residue-field extension and localization maps.
7. By `lem-weil-pbc-field-extension-base-change-faithfully-flat`,
   `lem-weil-pbc-flat-local-ring-maps`, and
   `lem-weil-pbc-flat-local-hom-faithfully-flat`, the map from the model fibre stalk
   to the given fibre stalk is faithfully flat. The injection supplied by
   `lem-weil-pbc-faithfully-flat-universally-injective` makes regularity descend.
   The descended element lies in the maximal ideal, so its singleton quotient is
   nonzero, as required by `def-weil-pbc-regular-sequence`.
8. Apply `lem-weil-pbc-grothendieck-regular-sequence-flat` to the Noetherian flat
   local model map and this singleton regular sequence in the closed fibre.
   Its prefix quotient is flat. By `lem-weil-pbc-flat-over-localization` it is
   flat over the unlocalized model base as well.
9. Apply `lem-weil-pbc-openness-of-flatness` to the one-generator, one-relation
   quotient module. Choose a principal neighbourhood of the model point and use
   the stalk and affine flatness criteria to make its entire quotient algebra flat.
10. Pull that principal open back to the original algebra. The explicit maps on
    tensor generators identify the base change of the model quotient with the
    quotient by the restricted section. Flatness follows from
    `lem-weil-pbc-flat-module-base-change`.
11. `lem-weil-pbc-flat-local-ring-maps` and the affine-stalk identifications show
    that every stalk map of the actual composite to S is flat. Apply
    `def-weil-flat-morphism`.
12. Adjoin an inverse variable and the section as one extra relation to the finite
    presentation. By `def-sbc-locally-finite-presentation` the composite is locally
    of finite presentation. The canonical spectrum of this principal quotient is
    the closed subscheme of `def-weil-closed-immersion`. Its section still has germ h,
    and h in the maximal ideal places x in that closed subscheme.
-/
theorem exists_affine_flat_hypersurface_of_fiber_regular
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (hflat : (f.stalkMap x).hom.Flat)
    (h : X.presheaf.stalk x) (hh : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hregular : Function.Injective
      (fun z : (f.fiber (f x)).presheaf.stalk (f.asFiber x) ↦
        (f.fiberStalkMap x).hom h * z)) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (a : Γ(X, U)),
      X.presheaf.germ U x hx a = h ∧
      x ∈ Set.range
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
          hU.fromSpec) ∧
      Flat
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
          hU.fromSpec ≫ f) ∧
      LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
          hU.fromSpec ≫ f) := by
  sorry

end AlgebraicGeometry
