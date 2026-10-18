/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Projective morphisms with zero-dimensional generic fibre

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc`,
lemma `lem-fin-projective-generically-finite` (blueprint: lem-fin-projective-generically-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective morphism over a Noetherian domain with generic fibre of dimension at most
zero is finite over a nonempty open of the base.

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-cbc`,
lemma `lem-fin-projective-generically-finite` (blueprint: lem-fin-projective-generically-finite).

Proof:
1. Projectivity implies properness [lem-pc-projective-proper], which is stable under
   base change [lem-pc-proper-base-change]. Thus the displayed generic fibre is of
   finite type over K. Dimension at most zero makes its underlying set finite
   [lem-weil-pbc-finite-type-dim-zero-artinian].
2. Choose the point p of Spec K. Every point in the ordinary fibre over its image
   lifts to the pullback [lem-weil-pbc-fibre-product-points], so this ordinary fibre
   is contained in the finite range of the pullback projection.
3. Apply Mathlib's proper finite-fibre neighbourhood theorem
   [lem-trf-proper-finite-fibre-finite-near] at that image. The resulting open
   contains the image of p, so it is nonempty.
-/
theorem exists_nonempty_open_isFinite_restrict_of_isProjective_generic_dim_le_zero
    (A K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {D : Scheme.{u}} (f : D ⟶ Spec (.of A)) [IsProjective f]
    (h : topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K))) : Scheme.{u}) ≤ 0) :
    ∃ U : (Spec (.of A)).Opens, (U : Set (Spec (.of A))).Nonempty ∧
      IsFinite (f ∣_ U) := by
  let η := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have : IsLocallyNoetherian (pullback f η : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f η)
  have : IsLocallyArtinian (pullback f η : Scheme.{u}) :=
    .of_topologicalKrullDim_le_zero h
  have : CompactSpace (pullback f η : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f η)
  have : Finite (pullback f η : Scheme.{u}) := finite_of_compact_of_discrete
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨U, hU, hfin⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f (η p) <| by
      refine (Set.finite_range (pullback.fst f η)).subset fun y hy ↦ ?_
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y p hy
      exact ⟨z, hz⟩
  exact ⟨U, ⟨η p, hU⟩, hfin⟩

end AlgebraicGeometry
