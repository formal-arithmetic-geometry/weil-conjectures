/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.Morphisms.ConnectedOpenEtaleRefinement
import WeilConjectures.AlgebraicGeometry.FibreOpenAffineReduction
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineEtaleFiniteLocallyFreeMultisection
import WeilConjectures.TraceFormula.FiniteLocallyFreeMultisectionConnectedOpen

/-! # Spreading a geometrically connected fibre open

Source: Stacks Project, more-morphisms.tex, Tag 055W, label
`lemma-fibre-geometrically-connected-reduced` (blueprint:
`lem-trf-geometrically-connected-fibre-open-spreading`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem geometricallyConnected_fiber_of_open_range
    {Y S W : Scheme.{u}} (h : Y ⟶ S) (j : W ⟶ Y) [IsOpenImmersion j]
    (s : S) (T : (h.fiber s).Opens)
    (hT : (h.fiberι s) ⁻¹ᵁ j.opensRange = T)
    [GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s)] :
    GeometricallyConnected ((j ≫ h).fiberToSpecResidueField s) := by
  let q := j ≫ h
  let d := Scheme.Hom.fiberMap (a := q) (b := h) j rfl (S.fromSpecResidueField s)
  have hd₁ : d ≫ h.fiberι s = q.fiberι s ≫ j := by
    simp [d, Scheme.Hom.fiberMap, Scheme.Hom.fiberι]
  have hd₂ : d ≫ h.fiberToSpecResidueField s = q.fiberToSpecResidueField s := by
    simp [d, Scheme.Hom.fiberMap, Scheme.Hom.fiberToSpecResidueField]
  have hd : IsPullback d (q.fiberι s) (h.fiberι s) j := by
    apply IsPullback.of_right (h₁₂ := h.fiberToSpecResidueField s) (h₂₂ := h)
    · rw [hd₂]
      exact (IsPullback.of_hasPullback q _).flip
    · exact hd₁
    · exact (IsPullback.of_hasPullback h _).flip
  have : IsOpenImmersion d := MorphismProperty.of_isPullback hd.flip inferInstance
  have hrange : Set.range d = (T : Set (h.fiber s)) := by
    rw [← hT]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨q.fiberι s z, congrArg (fun k ↦ k z) hd₁ |>.symm⟩
    · rintro ⟨w, hw⟩
      have hwq : w ∈ Set.range (q.fiberι s) := by
        rw [q.range_fiberι]
        change h (j w) = s
        rw [hw]
        exact (h.range_fiberι s).le ⟨x, rfl⟩
      obtain ⟨z, hz⟩ := hwq
      refine ⟨z, (h.fiberι s).isEmbedding.injective ?_⟩
      calc
        h.fiberι s (d z) = j (q.fiberι s z) := congrArg (fun k ↦ k z) hd₁
        _ = h.fiberι s x := by rw [hz, hw]
  let e := IsOpenImmersion.isoOfRangeEq d T.ι (by simpa using hrange)
  have he : e.hom ≫ T.ι ≫ h.fiberToSpecResidueField s =
      q.fiberToSpecResidueField s := by
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact hd₂
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso
    @GeometricallyConnected e.hom _).mpr inferInstance

/-- A geometrically connected open in a geometrically reduced flat finitely presented family
spreads to a quasi-compact open with geometrically connected fibres over an affine elementary
étale neighbourhood.

Source: Stacks Project, more-morphisms.tex, Tag 055W,
`lemma-fibre-geometrically-connected-reduced`.
Proof: first shrink the base to an affine neighbourhood and lift the prescribed fibre open to a
quasi-compact open.  Choose a Cohen--Macaulay point in that fibre and use the flat
quasifinite slice and the elementary étale finite-piece lemma to obtain a finite locally free
multisection.  The finite-locally-free multisection connected-open lemma then gives an open
with geometrically connected fibres and the prescribed special fibre.  Finally shrink to the
open image so that all fibres are nonempty, and then to an affine neighbourhood; flatness,
finite presentation, geometric reducedness, quasi-compactness, and the embedded fibre equality
are preserved by these restrictions and base changes.  The cited DAG nodes provide each step.
(blueprint: lem-trf-geometrically-connected-fibre-open-spreading) -/
theorem exists_geometricallyConnected_fibre_neighbourhood
    {Y S : Scheme.{u}} (h : Y ⟶ S) [Flat h]
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]
    [GeometricallyReduced h] (s : S) (T : (h.fiber s).Opens)
    [GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ (S₁ : Scheme.{u}) (a : S₁ ⟶ S) (s₁ : S₁) (hs : a s₁ = s),
      IsAffine S₁ ∧ Etale a ∧ IsIso (a.residueFieldMap s₁) ∧
      ∃ V : (pullback h a).Opens,
        IsCompact (V : Set ↥(pullback h a)) ∧
        GeometricallyConnected (V.ι ≫ pullback.snd h a) ∧
        (pullback.snd h a).fiberι s₁ ⁻¹ᵁ V =
          (pullback.map (pullback.snd h a) (S₁.fromSpecResidueField s₁)
              h (S.fromSpecResidueField (a s₁))
              (pullback.fst h a) (Spec.map (a.residueFieldMap s₁)) a
              (pullback.condition (f := h) (g := a)).symm
              (a.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
            eqToHom (congrArg h.fiber hs)) ⁻¹ᵁ T := by
  obtain ⟨S₀, hs₀, hS₀, W, hW, hflat, hlfp, hqc, hqs, hred, hT⟩ :=
    exists_affine_neighbourhood_quasiCompact_open_of_fiber_open h
      (fun t ↦ inferInstance) s T
  let s₀ : S₀ := ⟨s, hs₀⟩
  let g : W.toScheme ⟶ S₀.toScheme := W.ι ≫ pullback.snd h S₀.ι
  let j : W.toScheme ⟶ Y := W.ι ≫ pullback.fst h S₀.ι
  have : IsAffine S₀.toScheme := hS₀
  have : Flat g := hflat
  have : LocallyOfFinitePresentation g := hlfp
  have : QuasiCompact g := hqc
  have : QuasiSeparated g := hqs
  have hcomm : j ≫ h = g ≫ S₀.ι := by
    simp only [j, g, Category.assoc, pullback.condition]
  have hq : GeometricallyConnected ((j ≫ h).fiberToSpecResidueField s) :=
    geometricallyConnected_fiber_of_open_range h j s T hT
  have hsq : IsPullback (𝟙 W.toScheme) g (j ≫ h) S₀.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hcomm⟩
  have hg : GeometricallyConnected (g.fiberToSpecResidueField s₀) :=
    MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback hsq s₀) hq
  have : ConnectedSpace (g.fiber s₀) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (g.fiberToSpecResidueField s₀)
  obtain ⟨U, a, u₀, hu, hU, ha, hres, E, p, σ, hp, hσ, hpe, hps,
      hf, hfp, hfqc, hfqs, hfred, _, hfconn⟩ :=
    exists_affine_etale_finiteLocallyFree_multisection g hred s₀ inferInstance
  have : IsAffine U := hU
  have : Etale a := ha
  have : IsIso (a.residueFieldMap u₀) := hres
  have : Scheme.Hom.IsFiniteLocallyFree p := hp
  have : Flat (pullback.snd g a) := hf
  have : LocallyOfFinitePresentation (pullback.snd g a) := hfp
  have : QuasiCompact (pullback.snd g a) := hfqc
  have : QuasiSeparated (pullback.snd g a) := hfqs
  have hgc : GeometricallyConnected ((pullback.snd g a).fiberToSpecResidueField u₀) :=
    hfconn hg
  have : ConnectedSpace ((pullback.snd g a).fiber u₀) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      ((pullback.snd g a).fiberToSpecResidueField u₀)
  obtain ⟨X0, i, hi, hX0, hfull, hconn⟩ :=
    exists_quasiCompact_open_geometricallyConnected_fibres_of_finiteLocallyFree_multisection
      (pullback.snd g a) p σ hσ hfred u₀
      ⟨p.fiberι u₀ hpe.some, hpe.some, rfl⟩ hgc
  have : IsOpenImmersion i := hi
  have : CompactSpace X0 := hX0
  exact exists_affine_etale_refinement_of_connected_open h g j S₀.ι hcomm s₀ T hT
    a u₀ hu i hfull inferInstance hconn

end AlgebraicGeometry
