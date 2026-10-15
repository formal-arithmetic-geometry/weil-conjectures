/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBound
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension

/-!
# Quasi-finiteness descends for a finitely presented affine model

Source: Stacks Project, Limits, Tag 094M (lemma-descend-quasi-finite), in Situation
081D, specialized to affine schemes
(blueprint: lem-weil-pbc-descend-quasifinite-affine).

The tensor products are expressed as pushouts in `CommRingCat`. The canonical map
from the left factor is `pushout.inl`; `CommRingCat.pushoutCoconeIsColimit` identifies
this pushout and map with the algebra tensor product and its left inclusion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Quasi-finiteness of the limit affine base change descends to a stage at least `i₀`.
Source: Stacks Project, Limits, Tag 094M in Situation 081D
(blueprint: lem-weil-pbc-descend-quasifinite-affine).

Proof:
1. Restrict to the directed tail above `i₀`. A cocone on the tail extends uniquely to
   the original system by choosing common upper bounds. Thus its ring colimit is still
   `c.pt` (def-weil-pbc-category-colimit). By the pushout universal property, the colimit
   of the base-changed rings is the pushout at `c.pt`
   (lem-weil-pbc-fibre-product-affine-spectra). A finite presentation of `B₀` gives finitely
   many algebra generators after every base change (def-weil-pbc-finitely-presented-algebra,
   def-weil-pbc-finite-type-algebra).
2. Quasi-finiteness makes every singleton in every fibre open (pqf-def-quasifinite).
   Hence every subset is open and closed, and each nonempty irreducible closed subset
   is a singleton. Every fibre therefore has Krull dimension at most zero, including
   empty fibres, whose dimension is minus infinity (def-pc-scheme-fibre,
   lem-weil-pbc-fibre-product-affine-spectra, def-kun-topological-krull-dimension).
3. The canonical comparison between two successive base-changed rings is an isomorphism:
   both represent maps from the later base ring and `B₀` agreeing on the initial base.
   In particular it is surjective. Apply lem-weil-pbc-affine-limit-fibre-dimension-bound
   with `d = 0` to find a stage all of whose fibres have dimension at most zero.
4. At a point of such a fibre, dimension at the point is at most that of the whole
   fibre and is at least zero, hence equals zero (def-kun-topological-dimension-at-point).
   The finite-type zero-dimensional-fibre criterion gives quasi-finiteness at that point
   (lem-weil-pbc-ring-quasifinite-zero-fibre-dimension). The full affine source and target
   are allowable neighbourhoods, so the map is locally quasi-finite (pqf-def-quasifinite).
   It is affine (lem-weil-pbc-morphism-affine-schemes-affine), hence quasi-compact
   (lem-weil-pbc-affine-morphism-permanence). Now pqf-lem-qf-locqf-qc gives quasi-finiteness.
   For the zero ring there are no source points, and the pointwise assertion is vacuous.
-/
theorem descend_isQuasiFinite_affine
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (A : I ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : I) (B₀ : CommRingCat.{u}) (b₀ : A.obj i₀ ⟶ B₀)
    (hfp : b₀.hom.FinitePresentation)
    (hqf : Scheme.Hom.IsQuasiFinite (Spec.map (pushout.inl (c.ι.app i₀) b₀))) :
    ∃ (i : I) (hi : i₀ ≤ i),
      Scheme.Hom.IsQuasiFinite (Spec.map (pushout.inl (A.map (homOfLE hi)) b₀)) := by
  sorry

end AlgebraicGeometry
