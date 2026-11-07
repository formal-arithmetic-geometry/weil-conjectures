/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Submission.WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Etale fibres of a flat morphism of finite presentation

Source: Stacks Project, Tags 02GM, 02G8, and 02GK, and their pointwise algebra arguments.
(blueprint: lem-sbc-flat-fibre-etale-neighbourhoods)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- For a flat morphism locally of finite presentation, an etale fibre is equivalent to
etale source neighbourhoods at all points over the chosen target point.

Source: Stacks Project, Tag 02GM, morphisms-lemma-etale-flat-etale-fibres, together with Tags
02G8 and 02GK for unramifiedness and the pointwise etale criterion.
(blueprint: lem-sbc-flat-fibre-etale-neighbourhoods)

Proof: Suppose the fibre is etale. It is smooth of relative dimension zero, hence its
local dimension at every point is zero. For x over y the pointwise flat finite-presentation
smooth fibre criterion puts x in the smooth locus of f. The restriction of f to its smooth
locus is smooth: its smooth locus is the preimage of that of f under the open immersion,
which is the whole source. Apply exists_etale_open_of_smooth_of_fibre_dimension_zero to
this neighbourhood and the zero local fibre dimension to obtain an etale neighbourhood.
Conversely, base change each etale source neighbourhood to Spec(kappa(y)). These opens
cover the fibre, since its points identify with the points of X mapping to y. Their
morphisms to the residue field are etale by base change. Etaleness is local on the source,
so the whole fibre is etale. For an empty fibre both its etaleness and the universal
assertion hold. No finiteness of f or Noetherian condition on Y is used. -/
theorem etale_fibre_iff_forall_etale_neighbourhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (y : Y) :
    Etale (f.fiberToSpecResidueField y) ↔
      ∀ x : X, f x = y → ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)  := by
  classical
  constructor
  · intro hE x hxy
    subst y
    have := hE
    have hw : f.asFiber x ∈ (f.fiberToSpecResidueField (f x)).smoothLocus := by
      rw [(f.fiberToSpecResidueField (f x)).smoothLocus_eq_top]
      trivial
    have hx : x ∈ f.smoothLocus := by
      simpa using f.fiberι_mem_smoothLocus hw
    have hsm : Smooth (f.smoothLocus.ι ≫ f) := by
      apply (Scheme.Hom.smoothLocus_eq_top_iff).mp
      rw [← Scheme.Hom.preimage_smoothLocus_eq]
      ext z
      simp
    have hd : topologicalKrullDimAt (f.asFiber x) = 0 :=
      topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
        (f.fiberToSpecResidueField (f x)) 0 (f.asFiber x)
    obtain ⟨V, -, hxV, hV⟩ :=
      exists_etale_open_of_smooth_of_fibre_dimension_zero f x f.smoothLocus hx hsm hd
    exact ⟨V, hxV, hV⟩
  · intro h
    let g := f.fiberToSpecResidueField y
    let W (V : X.Opens) := (f.fiberι y) ⁻¹ᵁ V
    have hxy (w : f.fiber y) : f (f.fiberι y w) = y :=
      (f.range_fiberι y).subset ⟨w, rfl⟩
    choose V hwV hV using fun w : f.fiber y ↦ h (f.fiberι y w) (hxy w)
    apply IsZariskiLocalAtSource.of_iSup_eq_top (fun w ↦ W (V w))
    · apply top_unique
      intro w _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwV w⟩
    · intro w
      have hpb : IsPullback (f.fiberι y ∣_ V w) ((W (V w)).ι ≫ g)
          ((V w).ι ≫ f) (Y.fromSpecResidueField y) :=
        (isPullback_morphismRestrict (f.fiberι y) (V w)).paste_vert
          (IsPullback.of_hasPullback _ _)
      exact CategoryTheory.MorphismProperty.of_isPullback hpb (hV w)

end AlgebraicGeometry.Scheme
