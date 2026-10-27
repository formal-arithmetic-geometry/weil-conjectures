/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Sheaf.AlgebraicGeometry.FlatReducedSectionComponentOpen
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback

/-!
# Multisection components on a double overlap

Source: Stacks Project, Tag 057I, `lemma-descent-connected-fibres`, proof from the
construction of `X_Z` through the equality of the two component loci over `W`
(blueprint: lem-trf-multisection-component-overlap-neighbourhood).

The helpers name the concrete locus `C` and the canonical maps in this statement.
The double overlap is `pullback p p`, with structure map `pullback.fst p p ≫ p`.
No finiteness or surjectivity of `p` is assumed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- The concrete component locus `C` in `X ×_B Z` through the section `(σ, id)`.
Connected components of scheme fibres are expressed in the homeomorphic fibre subspaces.
Source: Stacks Project, Tag 057I, construction of `X_Z^0`
(blueprint: lem-trf-multisection-component-overlap-neighbourhood). -/
def multisectionComponentLocus {X B Z : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B)
    (σ : Z ⟶ X) (hσ : σ ≫ f = p) : Set ↥(pullback f p) :=
  {y | y ∈ connectedComponentIn
    (pullback.snd f p ⁻¹' {pullback.snd f p y})
    (pullback.lift σ (𝟙 Z) (hσ.trans (Category.id_comp p).symm) (pullback.snd f p y))}

/-- The two projections `Z ×_B Z → Z`, regarded as morphisms over `B`.
The index `0` selects the first projection and `1` the second.
Source: Stacks Project, Tag 057I, projections `pr_0, pr_1`
(blueprint: lem-trf-multisection-component-overlap-neighbourhood). -/
def multisectionOverlapProjection {B Z : Scheme.{u}} (p : Z ⟶ B) (i : Fin 2) :
    Over.mk (pullback.fst p p ≫ p) ⟶ Over.mk p :=
  if i = 0 then Over.homMk (pullback.fst p p) rfl
  else Over.homMk (pullback.snd p p) pullback.condition.symm

/-- The map `a_i : X ×_B (Z ×_B Z) → X ×_B Z` induced by projection `i`.
Source: Stacks Project, Tag 057I, maps `1_X × pr_i`
(blueprint: lem-trf-multisection-component-overlap-neighbourhood). -/
def multisectionOverlapMap {X B Z : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B)
    (i : Fin 2) : pullback f (pullback.fst p p ≫ p) ⟶ pullback f p :=
  baseChangeMap f (multisectionOverlapProjection p i)

/-- The section `s_i` of `X ×_B (Z ×_B Z) → Z ×_B Z` induced by `σ` and projection `i`.
It is the universal lift of `(σ ∘ pr_i, id)`; its compatibility uses `σ ≫ f = p`
and the defining equation of a morphism over `B`.
Source: Stacks Project, Tag 057I, sections `s_0, s_1`
(blueprint: lem-trf-multisection-component-overlap-neighbourhood). -/
def multisectionOverlapSection {X B Z : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B)
    (σ : Z ⟶ X) (hσ : σ ≫ f = p) (i : Fin 2) :
    pullback p p ⟶ pullback f (pullback.fst p p ≫ p) :=
  pullback.lift ((multisectionOverlapProjection p i).left ≫ σ) (𝟙 (pullback p p))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t ↦ (multisectionOverlapProjection p i).left ≫ t) hσ).trans
        ((Over.w (multisectionOverlapProjection p i)).trans (Category.id_comp _).symm)))

/-- Multisection component loci are open, commute with the two overlap projections,
and coincide over an open neighbourhood of every geometrically connected fibre.

Source: Stacks Project, Tag 057I, `lemma-descent-connected-fibres`, the part of its
proof ending with equality over `W`. This part imposes no hypothesis on `p`.

Proof:
1. Base change makes `g : X ×_B Z → Z` flat and of finite presentation
   (`lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`).
   Its fibre at `z` is the base change of `X_(p(z))` to `κ(z)` by the pullback
   universal property (`def-pc-fibre-product`, `def-pc-scheme-fibre`). Further field
   extensions remain reduced, so its fibres are geometrically reduced
   (`def-pc-geometrically-irreducible`). The lift `(σ, id)` is a section.
2. `lem-trf-flat-reduced-section-component-open` gives openness of `C`.
   Local finite presentation implies local finite type (`def-sbc-locally-finite-presentation`,
   `def-weil-finite-type-morphism`). Each square defined by `a_i` is cartesian
   (`def-pc-base-change`), with the prescribed compatible section. Therefore
   `lem-sbc-section-component-cartesian` identifies `a_i⁻¹(C)` with the component
   locus of `s_i`. Both inverse images are open by continuity.
3. At every point `r` above `b₀`, the fibre is `X_b₀` extended to `κ(r)`
   (`def-pc-fibre-product`, `def-pc-scheme-fibre`). Geometric connectedness
   (`def-pc-geometrically-irreducible`) makes it connected. Both section components
   are the whole fibre, so each section point belongs to the other's component.
4. Take `W = s₀⁻¹(a₁⁻¹(C)) ∩ s₁⁻¹(a₀⁻¹(C))`. It is open by continuity,
   contains the entire inverse image of `b₀`, and gives both incidence inclusions.
   This construction needs neither finiteness nor nonemptiness of that inverse image.
5. Over `r ∈ W` the two connected components intersect. Their union is connected,
   and maximality of connected components forces them to coincide. Using step 2
   fibre by fibre gives the asserted equality after intersection with `h⁻¹(W)`.

(blueprint: lem-trf-multisection-component-overlap-neighbourhood) -/
theorem multisection_component_overlap_neighbourhood {X B Z : Scheme.{u}}
    (f : X ⟶ B) (p : Z ⟶ B) (σ : Z ⟶ X) (hσ : σ ≫ f = p)
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hred : ∀ b : B, GeometricallyReduced (f.fiberToSpecResidueField b)) :
    IsOpen (multisectionComponentLocus f p σ hσ) ∧
    (∀ i : Fin 2,
      multisectionOverlapMap f p i ⁻¹' multisectionComponentLocus f p σ hσ =
        {x : ↥(pullback f (pullback.fst p p ≫ p)) | x ∈ connectedComponentIn
          (pullback.snd f (pullback.fst p p ≫ p) ⁻¹'
            {pullback.snd f (pullback.fst p p ≫ p) x})
          (multisectionOverlapSection f p σ hσ i
            (pullback.snd f (pullback.fst p p ≫ p) x))}) ∧
    ∀ b₀ : B, GeometricallyConnected (f.fiberToSpecResidueField b₀) →
      ∃ W : (pullback p p).Opens,
        (pullback.fst p p ≫ p) ⁻¹' {b₀} ⊆ (W : Set ↥(pullback p p)) ∧
        multisectionOverlapSection f p σ hσ 0 '' (W : Set ↥(pullback p p)) ⊆
          multisectionOverlapMap f p 1 ⁻¹' multisectionComponentLocus f p σ hσ ∧
        multisectionOverlapSection f p σ hσ 1 '' (W : Set ↥(pullback p p)) ⊆
          multisectionOverlapMap f p 0 ⁻¹' multisectionComponentLocus f p σ hσ ∧
        (pullback.snd f (pullback.fst p p ≫ p) ⁻¹' (W : Set ↥(pullback p p))) ∩
            (multisectionOverlapMap f p 0 ⁻¹' multisectionComponentLocus f p σ hσ) =
          (pullback.snd f (pullback.fst p p ≫ p) ⁻¹' (W : Set ↥(pullback p p))) ∩
            (multisectionOverlapMap f p 1 ⁻¹' multisectionComponentLocus f p σ hσ) := by
  let g := pullback.snd f p
  let s : Z ⟶ pullback f p :=
    pullback.lift σ (𝟙 Z) (hσ.trans (Category.id_comp p).symm)
  have hs : s ≫ g = 𝟙 Z := pullback.lift_snd _ _ _
  have : GeometricallyReduced f := ⟨
    geometrically_iff_forall_fiberToSpecResidueField.mpr
      (fun b ↦ (hred b).geometrically_isReduced)⟩
  have hopen : IsOpen (multisectionComponentLocus f p σ hσ) :=
    isOpen_section_component_of_flat_of_geometricallyReduced_fibers g s hs
      (fun z ↦ inferInstance)
  let q := pullback.fst p p ≫ p
  let h := pullback.snd f q
  let a := multisectionOverlapMap f p
  let t := multisectionOverlapSection f p σ hσ
  let C := multisectionComponentLocus f p σ hσ
  have ht (i : Fin 2) : t i ≫ h = 𝟙 _ := pullback.lift_snd _ _ _
  have ht_apply (i : Fin 2) (r : ↥(pullback p p)) : h (t i r) = r := by
    rw [← Scheme.Hom.comp_apply, ht]
    rfl
  have hcompat (i : Fin 2) :
      t i ≫ a i = (multisectionOverlapProjection p i).left ≫ s := by
    apply pullback.hom_ext
    · simp only [multisectionOverlapSection, Over.mk_left, multisectionOverlapMap,
        baseChangeMap, Over.mk_hom, Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
        Category.comp_id, t, a, s]
    · simp only [multisectionOverlapSection, Over.mk_left, multisectionOverlapMap,
        baseChangeMap, Over.mk_hom, Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
        limit.lift_π_assoc, cospan_right, Category.comp_id, t, a, s]
      exact Category.id_comp _
  have hcomp (i : Fin 2) : a i ⁻¹' C =
      {x | x ∈ connectedComponentIn (h ⁻¹' {h x}) (t i (h x))} :=
    section_component_preimage_of_isPullback g s hs (a i) h
      (multisectionOverlapProjection p i).left
      (isPullback_baseChangeMap f (multisectionOverlapProjection p i))
      (t i) (ht i) (hcompat i)
  refine ⟨hopen, hcomp, ?_⟩
  intro b₀ hb₀
  let W : (pullback p p).Opens :=
    ⟨t 0 ⁻¹' (a 1 ⁻¹' C) ∩ t 1 ⁻¹' (a 0 ⁻¹' C),
      ((hopen.preimage (a 1).continuous).preimage (t 0).continuous).inter
        ((hopen.preimage (a 0).continuous).preimage (t 1).continuous)⟩
  have hwhole (r : ↥(pullback p p)) (hr : q r = b₀) (i j : Fin 2) :
      t i r ∈ a j ⁻¹' C := by
    have hc : GeometricallyConnected (f.fiberToSpecResidueField (q r)) := by
      rwa [hr]
    have hcf : ConnectedSpace (h.fiber r) :=
      hc.geometrically_connectedSpace _ _ _
        (isPullback_fiberToSpecResidueField_of_isPullback
          (IsPullback.of_hasPullback f q) r)
    have hpre : _root_.IsPreconnected (h ⁻¹' {r}) :=
      isPreconnected_iff_preconnectedSpace.mpr
        ((h.fiberHomeo r).connectedSpace_iff.mp hcf).toPreconnectedSpace
    rw [hcomp]
    change t i r ∈ connectedComponentIn (h ⁻¹' {h (t i r)}) (t j (h (t i r)))
    rw [ht_apply, hpre.connectedComponentIn (ht_apply j r)]
    exact ht_apply i r
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact ⟨hwhole r hr 0 1, hwhole r hr 1 0⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hr.1
  · rintro _ ⟨r, hr, rfl⟩
    exact hr.2
  · ext x
    change (h x ∈ W ∧ x ∈ a 0 ⁻¹' C) ↔ (h x ∈ W ∧ x ∈ a 1 ⁻¹' C)
    by_cases hx : h x ∈ W
    · have hinc : t 0 (h x) ∈ connectedComponentIn (h ⁻¹' {h x}) (t 1 (h x)) := by
        have hi : t 0 (h x) ∈ a 1 ⁻¹' C := hx.1
        rw [hcomp] at hi
        change t 0 (h x) ∈ connectedComponentIn
          (h ⁻¹' {h (t 0 (h x))}) (t 1 (h (t 0 (h x)))) at hi
        simpa only [ht_apply] using hi
      rw [hcomp, hcomp]
      change (h x ∈ W ∧ x ∈ connectedComponentIn (h ⁻¹' {h x}) (t 0 (h x))) ↔
        (h x ∈ W ∧ x ∈ connectedComponentIn (h ⁻¹' {h x}) (t 1 (h x)))
      rw [connectedComponentIn_eq hinc]
    · simp only [hx, false_and]

end

end AlgebraicGeometry
