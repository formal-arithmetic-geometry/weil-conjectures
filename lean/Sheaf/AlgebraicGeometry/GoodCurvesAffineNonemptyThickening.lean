/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.GoodCurvesReducedAffineNonemptyThickening
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# Good curve diagrams over an affine base

Source: Stacks Project, More on Morphisms, Tag 0GK7, proof through the shrinking
which makes every W_i → T_i surjective.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Construct the curve presentation and a thickening locus which meets every fibre
of each smooth curve. Density is not asserted here.

Source: Stacks Project, More on Morphisms, Tag 0GK7, proof through the sentence
"Shrinking S once more we can assume W_i → T_i is surjective for all i".
(blueprint: lem-weil-pbc-good-curves-affine-nonempty-thickening)

Proof: Replace the affine base by its nilradical subscheme R. The reduction theorem
makes R reduced and its inclusion r a finite radicial surjection and a homeomorphism.
It also makes R affine. Lift η uniquely; the homeomorphism transports the irreducible
component and generic-point property. After base change, the induced homeomorphism of
total spaces restricts to a homeomorphism of fibres, preserving their Krull dimension.
Apply the reduced affine presentation. The image U of its open B in R is open in S.
The induced B → U is the base change of r, so it is finite, surjective and radicial.
Compose the cover with it. Cartesian pasting identifies the two target pullbacks;
transport ν and the open W along this isomorphism. The square of inverse-image opens
is cartesian, so its projection is isomorphic to the old thickening. The pointwise
image formula transports the nonempty-fibre witnesses and all commuting equations. -/
theorem exists_good_curves_affine_nonempty_thickening
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ (i : Fin n) (s : T i),
            ∃ y : (j i ≫ p i).fiber s,
              ((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) y ∈ W) ∧
          IsThickening (pullback.snd ν W.ι) := by
  let R := S.nilradical.subscheme
  let r : R ⟶ S := S.nilradical.subschemeι
  have : Surjective r :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism S).2.2.1
  have hr : IsHomeomorph r :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨r.isEmbedding, r.surjective⟩
  have : IsAffine R := isAffine_of_isAffineHom r
  have : IsReduced R :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism S).1
  obtain ⟨ηR, hηR⟩ := r.surjective η
  obtain ⟨Z, hZ, hηZ⟩ := hη
  have hηR' : ∃ Z' ∈ irreducibleComponents R, IsGenericPoint ηR Z' := by
    refine ⟨r ⁻¹' Z, preimage_mem_irreducibleComponents hZ hr.isOpenEmbedding
      ⟨η, hηZ.mem, ⟨ηR, hηR⟩⟩, ?_⟩
    rw [isGenericPoint_iff_specializes]
    intro x
    change ηR ⤳ x ↔ r x ∈ Z
    rw [← hr.isInducing.specializes_iff, hηR]
    exact hηZ.specializes_iff_mem
  let fR := pullback.snd f r
  let k := pullback.fst f r
  have : Surjective k := inferInstance
  have hk : IsHomeomorph k :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨k.isEmbedding, k.surjective⟩
  have hfR : fR ≫ r = k ≫ f := pullback.condition.symm
  have hdimR : topologicalKrullDim (fR.fiber ηR) ≤ 1 := by
    let e : (fR ⁻¹' {ηR}) ≃ₜ (f ⁻¹' {η}) :=
      hk.homeomorph.subtype (fun x ↦ by
        change fR x = ηR ↔ f (k x) = η
        rw [← hηR, ← Scheme.Hom.comp_apply, ← hfR, Scheme.Hom.comp_apply]
        exact hr.injective.eq_iff.symm)
    let E := (fR.fiberHomeo ηR).trans (e.trans (f.fiberHomeo η).symm)
    rw [E.isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  obtain ⟨B, hηB, V, g, hgfin, hgsurj, hginj, n, T, Y, Ybar, t, j, p, ν,
    hνfin, hνsurj, hcomm, ht, hj, hq, hp, W, hWmeet, hWthick⟩ :=
    exists_good_curves_reduced_affine_nonempty_thickening fR ηR hηR' hdimR
  let U : S.Opens := ⟨r '' (B : Set R), hr.isOpenMap _ B.isOpen⟩
  have hBU : B ≤ r ⁻¹ᵁ U := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  let b : B.toScheme ⟶ U.toScheme := r.resLE U B hBU
  have hbpb : IsPullback b B.ι U.ι r := by
    apply IsOpenImmersion.isPullback
    · simp [b]
    · simp only [Scheme.Opens.opensRange_ι]
      ext x
      change (∃ y, y ∈ B ∧ r y = r x) ↔ x ∈ B
      constructor
      · rintro ⟨y, hy, heq⟩
        exact hr.injective heq ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
  have : IsFinite b := MorphismProperty.of_isPullback hbpb.flip inferInstance
  have : Surjective b := MorphismProperty.of_isPullback hbpb.flip inferInstance
  have : UniversallyInjective b := MorphismProperty.of_isPullback hbpb.flip inferInstance
  let g' := g ≫ b
  have hg' : g' ≫ U.ι = g ≫ B.ι ≫ r := by simp [g', b]
  let e : pullback fR (g ≫ B.ι) ≅ pullback f (g' ≫ U.ι) :=
    (((IsPullback.of_hasPullback fR (g ≫ B.ι)).flip.paste_vert
      (IsPullback.of_hasPullback f r).flip).flip.isoPullback) ≪≫
      pullback.congrHom rfl (by simpa only [Category.assoc] using hg'.symm)
  have hesnd : e.hom ≫ pullback.snd f (g' ≫ U.ι) = pullback.snd fR (g ≫ B.ι) := by
    simp [e]
  let ν' := ν ≫ e.hom
  let W' := e.hom ''ᵁ W
  have hνfin' : IsFinite ν' := by have := hνfin; infer_instance
  have hνsurj' : Surjective ν' := by have := hνsurj; infer_instance
  have hWthick' : IsThickening (pullback.snd ν' W'.ι) := by
    have : IsClosedImmersion (ν ∣_ W) := by
      have := hWthick.1
      change IsClosedImmersion ((pullbackRestrictIsoRestrict ν W).inv ≫ pullback.snd ν W.ι)
      infer_instance
    have : Surjective (ν ∣_ W) := by
      have := hWthick.2
      change Surjective ((pullbackRestrictIsoRestrict ν W).inv ≫ pullback.snd ν W.ι)
      infer_instance
    let k := (ν ∣_ W) ≫ (e.hom.isoImage W).hom
    have hk : IsClosedImmersion k := inferInstance
    have hks : Surjective k := inferInstance
    have hpb : IsPullback k (ν ⁻¹ᵁ W).ι W'.ι ν' := by
      apply IsOpenImmersion.isPullback
      · simp [k, W', ν', Category.assoc]
      · simp [ν', W']
    have he : hpb.isoPullback.inv ≫ k = pullback.fst W'.ι ν' :=
      hpb.isoPullback_inv_fst
    have hk' : IsClosedImmersion (pullback.fst W'.ι ν') := by
      rw [← he]
      infer_instance
    have hks' : Surjective (pullback.fst W'.ι ν') := by
      rw [← he]
      infer_instance
    constructor
    · have heq : (pullbackSymmetry ν' W'.ι).hom ≫ pullback.fst W'.ι ν' =
          pullback.snd ν' W'.ι := by simp
      rw [← heq]
      infer_instance
    · have heq : (pullbackSymmetry ν' W'.ι).hom ≫ pullback.fst W'.ι ν' =
          pullback.snd ν' W'.ι := by simp
      rw [← heq]
      infer_instance
  refine ⟨U, ⟨ηR, hηB, hηR⟩, V, g', ?_, ?_, ?_, n, T, Y, Ybar, t, j, p, ν',
    hνfin', hνsurj', ?_, ht, hj, hq, hp, W', ?_, hWthick'⟩
  · have := hgfin
    infer_instance
  · have := hgsurj
    infer_instance
  · exact MorphismProperty.comp_mem (@UniversallyInjective) g b hginj inferInstance
  · intro i
    simpa only [ν', Category.assoc, hesnd] using hcomm i
  · intro i s
    obtain ⟨y, hy⟩ := hWmeet i s
    refine ⟨y, ?_⟩
    exact ⟨((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) y, hy, rfl⟩

end AlgebraicGeometry

