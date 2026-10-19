/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.RingTheory.ClosedPointDimensionLocalRing
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen
import Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.DepthQuotientNonzerodivisor
import Sheaf.AlgebraicGeometry.Morphisms.FibreRegularElementFlatHypersurface

/-!
# A flat quasi-finite slice through a closed Cohen-Macaulay fibre point

Source: Stacks Project, More on Morphisms, Tag 0570, `lemma-slice-CM`, specialized
to a globally flat morphism and forgetting regularity of the immersion.
(blueprint: lem-trf-cm-closed-point-flat-quasifinite-slice)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed Cohen-Macaulay fibre point lies on a flat, locally finitely presented,
locally quasi-finite slice whose designated fibre is a singleton.

Source: Stacks Project, More on Morphisms, Tag 0570, `lemma-slice-CM`.
(blueprint: lem-trf-cm-closed-point-flat-quasifinite-slice)

Proof plan:
1. Strengthen equality of depth and dimension to depth at least dimension and induct
   strongly on the finite local-ring dimension, uniformly over flat locally finitely
   presented morphisms. Finiteness is
   `lem-weil-pbc-noetherian-local-finite-krull-dimension`.
2. In dimension zero choose finite-presentation affine charts. Identify their fibre
   with the spectrum of the tensor product using `lem-weil-pbc-fibre-product-affine-spectra`.
   The closed-point formula `lem-weil-pbc-closed-point-dimension-local-ring` identifies
   local fibre dimension with local-ring dimension. Apply
   `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension` to get quasi-finiteness at the point.
3. Use `lem-sc-quasi-finite-points-open` and
   `lem-weil-pbc-quasi-finite-at-point-isolated` to restrict to an open neighbourhood
   whose fibre is the singleton. The subspace topology of `def-pc-scheme-fibre` supplies
   that open. `lem-weil-pbc-lqf-restriction-to-opens` preserves local quasi-finiteness.
   Open restrictions preserve flatness and local finite presentation: stalk maps are
   unchanged and principal localizations of finite presentations are finitely presented.
4. In positive dimension, `def-weil-pbc-depth` and `def-weil-pbc-regular-sequence`
   give a nonzerodivisor in the fibre maximal ideal. Lift it to the source stalk using
   `lem-sbc-scheme-fibre-stalk-quotient`; a unit cannot map into the fibre maximal ideal.
   `lem-trf-fibre-regular-element-flat-hypersurface` cuts out a flat locally finitely
   presented hypersurface through the point.
5. Localization commutes with quotient, so its fibre local ring is the original fibre
   local ring modulo the chosen nonzerodivisor. This follows by writing the fibre ring
   as the source stalk modulo the extended base maximal ideal, using
   `lem-sbc-scheme-fibre-stalk-quotient`. The point stays closed in this closed fibre
   subscheme (`def-weil-closed-immersion`).
6. `lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm` gives a Noetherian local quotient
   of dimension one less and depth at least that dimension. Apply induction to the
   hypersurface and compose the slice map with its inclusion in the source. The map
   to the base and its flatness, local finite presentation, local quasi-finiteness,
   and singleton fibre are exactly those supplied by induction.
-/
theorem exists_flat_locallyQuasiFinite_slice_of_closed_fibre_depth_eq_ringKrullDim
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S) (x : f.fiber s) (hx : x ∈ closedPoints (f.fiber s))
    [IsNoetherianRing ((f.fiber s).presheaf.stalk x)]
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber s).presheaf.stalk x)
        ((f.fiber s).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber s).presheaf.stalk x)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : (i ≫ f).fiber s),
      i ((i ≫ f).fiberι s z) = f.fiberι s x ∧
      Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
      (∀ z' : (i ≫ f).fiber s, z' = z) ∧ (i ≫ f).IsLocallyQuasiFinite := by
  sorry

end AlgebraicGeometry
