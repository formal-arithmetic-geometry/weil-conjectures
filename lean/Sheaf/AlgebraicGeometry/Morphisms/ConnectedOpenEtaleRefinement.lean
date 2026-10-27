/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Refining a connected open over an elementary étale neighbourhood

Source: Stacks Project, Tag 055W, final paragraph of the proof of
`lemma-fibre-geometrically-connected-reduced`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem range_fst_of_isPullback
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd p, (congrArg (fun k ↦ k p) H.w).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨H.isoPullback.inv z, ?_⟩
    calc
      fst (H.isoPullback.inv z) = pullback.fst f g z :=
        congrArg (fun k ↦ k z) H.isoPullback_inv_fst
      _ = x := hz

private theorem isPullback_fiberMap
    {X Y B P : Scheme.{u}} {r : X ⟶ B} {f : Y ⟶ B}
    (i : X ⟶ Y) (hi : i ≫ f = r) (a : P ⟶ B) :
    IsPullback (Scheme.Hom.fiberMap i hi a) (pullback.fst r a) (pullback.fst f a) i := by
  apply IsPullback.of_right (h₁₂ := pullback.snd f a) (h₂₂ := f)
  · simpa [Scheme.Hom.fiberMap, hi] using (IsPullback.of_hasPullback r a).flip
  · simp [Scheme.Hom.fiberMap]
  · exact (IsPullback.of_hasPullback f a).flip

private theorem fiberι_eqToHom {Y S : Scheme.{u}} (h : Y ⟶ S)
    {s t : S} (e : s = t) :
    eqToHom (congrArg h.fiber e) ≫ h.fiberι t = h.fiberι s := by
  cases e
  simp

/-- A quasi-compact open whose nonempty fibres are geometrically connected, and which contains
an entire specified nonempty fibre, can be restricted to an affine open in its open image.
The resulting family has geometrically connected fibres everywhere. The conclusion records
its inclusion into the original family and the exact prescribed fibre open.

Source: Stacks Project, Tag 055W, final paragraph of the proof of
`lemma-fibre-geometrically-connected-reduced` (open image and final affine shrinking).
Proof: let `r = i ≫ pullback.snd g a`. This map is flat and locally of finite presentation,
so its image is open. The isomorphism on the fibre induced by `i` and the assumed nonempty
fibre show that this image contains `u`. Choose an affine open `B` containing `u` inside that
image. Set `S₁ = B`, and let `V` be the image of `X0 ×[U] B` in
`Y ×[S] B`, using `B → U → S₀ → S`. This map is an open immersion: the square over the
open immersion `j` is cartesian, since `b` is a monomorphism. Its source is quasi-compact:
`X0 → U` is quasi-compact because `X0` is quasi-compact and the affine `U` is quasi-separated;
base change to the affine `B` preserves this. Each fibre is nonempty by the choice of `B`,
and is geometrically connected by the given fibrewise assertion and base change. The
composite base map is étale, and its residue map at the chosen point is an isomorphism,
since both open immersions induce residue-field isomorphisms. On the distinguished fibre,
`i` is an isomorphism, so the inverse image of `V` is the whole base change of `W`.
The cartesian square over `j` identifies this with the inverse image of `j.opensRange`;
its inverse image in the original fibre is `T` by `hT`. Naturality of the two fibre
projections identifies this inverse image with the explicit pullback map in the conclusion.
No reducedness, finite multisection, or existence of a connected open is asserted here;
those are inputs to this final refinement step.
(blueprint: lem-trf-connected-open-etale-refinement) -/
theorem exists_affine_etale_refinement_of_connected_open
    {Y S W S₀ U X0 : Scheme.{u}} (h : Y ⟶ S) (g : W ⟶ S₀)
    (j : W ⟶ Y) (b : S₀ ⟶ S) [IsOpenImmersion j] [IsOpenImmersion b]
    (hcomm : j ≫ h = g ≫ b) [Flat g] [LocallyOfFinitePresentation g]
    (s₀ : S₀) (T : (h.fiber (b s₀)).Opens)
    (hT : (h.fiberι (b s₀)) ⁻¹ᵁ j.opensRange = T)
    [IsAffine U] (a : U ⟶ S₀) [Etale a] (u₀ : U) (hu : a u₀ = s₀)
    [IsIso (a.residueFieldMap u₀)]
    (i : X0 ⟶ pullback g a) [IsOpenImmersion i] [CompactSpace X0]
    (hfull : IsIso (Scheme.Hom.fiberMap (a := i ≫ pullback.snd g a)
      (b := pullback.snd g a) i rfl (U.fromSpecResidueField u₀)))
    (hne : Nonempty ((pullback.snd g a).fiber u₀))
    (hconn : ∀ t : U, Set.Nonempty (Set.range ((i ≫ pullback.snd g a).fiberι t)) →
      GeometricallyConnected ((i ≫ pullback.snd g a).fiberToSpecResidueField t)) :
    ∃ (S₁ : Scheme.{u}) (A : S₁ ⟶ S) (s₁ : S₁) (hs : A s₁ = b s₀),
      IsAffine S₁ ∧ Etale A ∧ IsIso (A.residueFieldMap s₁) ∧
      ∃ V : (pullback h A).Opens,
        IsCompact (V : Set ↥(pullback h A)) ∧
        GeometricallyConnected (V.ι ≫ pullback.snd h A) ∧
        (pullback.snd h A).fiberι s₁ ⁻¹ᵁ V =
          (pullback.map (pullback.snd h A) (S₁.fromSpecResidueField s₁)
              h (S.fromSpecResidueField (A s₁))
              (pullback.fst h A) (Spec.map (A.residueFieldMap s₁)) A
              (pullback.condition (f := h) (g := A)).symm
              (A.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
            eqToHom (congrArg h.fiber hs)) ⁻¹ᵁ T := by
  let f := pullback.snd g a
  let r := i ≫ f
  let A₀ := a ≫ b
  let q := pullback.snd h A₀
  let k₀ : pullback g a ⟶ pullback h A₀ :=
    pullback.lift (pullback.fst g a ≫ j) f (by
      simp only [f, A₀, Category.assoc, hcomm, ← pullback.condition_assoc])
  have hk₀ : IsPullback k₀ (pullback.fst g a) (pullback.fst h A₀) j := by
    have H : IsPullback (𝟙 W) g (j ≫ h) b :=
      IsPullback.of_horiz_isIso_mono ⟨by simpa using hcomm⟩
    have Hp := (IsPullback.of_hasPullback g a).paste_horiz H
    apply IsPullback.of_right (h₁₂ := q) (h₂₂ := h)
    · simpa [k₀, f, A₀, q] using Hp.flip
    · simp [k₀]
    · exact (IsPullback.of_hasPullback h A₀).flip
  have : IsOpenImmersion k₀ := MorphismProperty.of_isPullback hk₀.flip inferInstance
  let I := i ≫ k₀
  have hIq : I ≫ q = r := by simp [I, k₀, q, r, f]
  have hfull_range (v : ↥(pullback g a)) (hv : f v = u₀) : v ∈ Set.range i := by
    obtain ⟨z, hz⟩ := (f.range_fiberι u₀).ge hv
    let d := Scheme.Hom.fiberMap (a := r) (b := f) i rfl (U.fromSpecResidueField u₀)
    have : IsIso d := hfull
    obtain ⟨w, hw⟩ := d.surjective z
    refine ⟨r.fiberι u₀ w, ?_⟩
    have he : d ≫ f.fiberι u₀ = r.fiberι u₀ ≫ i := by
      simp [d, Scheme.Hom.fiberMap, Scheme.Hom.fiberι]
    calc
      i (r.fiberι u₀ w) = f.fiberι u₀ (d w) :=
        (congrArg (fun k ↦ k w) he).symm
      _ = v := by rw [hw, hz]
  have hrange_u (x : ↥(pullback h A₀)) (hx : q x = u₀) :
      x ∈ Set.range I ↔ pullback.fst h A₀ x ∈ Set.range j := by
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨pullback.fst g a (i z), ?_⟩
      have he : I ≫ pullback.fst h A₀ = i ≫ pullback.fst g a ≫ j := by
        simp [I, k₀]
      exact (congrArg (fun t ↦ t z) he).symm
    · intro hxj
      obtain ⟨v, hv⟩ := (range_fst_of_isPullback hk₀).ge hxj
      have hvu : f v = u₀ := by
        have he : k₀ ≫ q = f := by simp [k₀, q]
        rw [← he, Scheme.Hom.comp_apply, hv, hx]
      obtain ⟨z, hz⟩ := hfull_range v hvu
      exact ⟨z, by simp [I, hz, hv]⟩
  have hu_image : u₀ ∈ Set.range r := by
    let z := hne.some
    obtain ⟨x, hx⟩ := hfull_range (f.fiberι u₀ z) ((f.range_fiberι u₀).le ⟨z, rfl⟩)
    refine ⟨x, ?_⟩
    change f (i x) = u₀
    rw [hx]
    exact (f.range_fiberι u₀).le ⟨z, rfl⟩
  let O : U.Opens := ⟨Set.range r, r.isOpenMap.isOpen_range⟩
  obtain ⟨B, hB, huB, hBO⟩ := exists_isAffineOpen_mem_and_subset
    (show u₀ ∈ O from hu_image)
  have : IsAffine B.toScheme := hB
  let s₁ : B := ⟨u₀, huB⟩
  let A := B.ι ≫ A₀
  let e := pullbackLeftPullbackSndIso h A₀ B.ι
  let d := Scheme.Hom.fiberMap I hIq B.ι
  have hd := isPullback_fiberMap I hIq B.ι
  have : IsOpenImmersion I := inferInstance
  have : IsOpenImmersion d := MorphismProperty.of_isPullback hd.flip inferInstance
  let k := d ≫ e.hom
  let L := e.inv ≫ pullback.fst q B.ι
  have hkq : k ≫ pullback.snd h A = pullback.snd r B.ι := by
    simp [k, e, d, Scheme.Hom.fiberMap, A, q]
  have hkL : k ≫ L = pullback.fst r B.ι ≫ I := by
    simp [k, L, d, Scheme.Hom.fiberMap]
  have hLq : L ≫ q = pullback.snd h A ≫ B.ι := by
    simp [L, q, e, A]
  have hLfst : L ≫ pullback.fst h A₀ = pullback.fst h A := by
    simp [L, q, e, A]
  have hrange_k (x : ↥(pullback h A)) : x ∈ Set.range k ↔ L x ∈ Set.range I := by
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨pullback.fst r B.ι z, (congrArg (fun t ↦ t z) hkL).symm⟩
    · intro hx
      have hx' : pullback.fst q B.ι (e.inv x) ∈ Set.range I := hx
      obtain ⟨z, hz⟩ := (range_fst_of_isPullback hd).ge hx'
      refine ⟨z, ?_⟩
      change e.hom (d z) = x
      rw [hz]
      exact congrArg (fun t ↦ t x) e.inv_hom_id
  have hgeo : GeometricallyConnected (pullback.snd r B.ι) := by
    rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
    intro t
    obtain ⟨x, hx⟩ := hBO t.property
    have hne' : Set.Nonempty (Set.range (r.fiberι (B.ι t))) := by
      obtain ⟨z, _⟩ := (r.range_fiberι (B.ι t)).ge hx
      exact ⟨r.fiberι _ z, z, rfl⟩
    exact MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback r B.ι) t) (hconn (B.ι t) hne')
  have : CompactSpace ↥(pullback r B.ι) := inferInstance
  have : IsOpenImmersion k := inferInstance
  have hs : A s₁ = b s₀ := by
    change b (a u₀) = b s₀
    rw [hu]
  have : IsIso (A.residueFieldMap s₁) := by
    dsimp only [A, A₀]
    simp only [Scheme.residueFieldMap_comp, Category.assoc]
    change IsIso (b.residueFieldMap (a u₀) ≫ a.residueFieldMap u₀ ≫
      B.ι.residueFieldMap s₁)
    infer_instance
  refine ⟨B.toScheme, A, s₁, hs, hB, inferInstance, inferInstance,
    k.opensRange, ?_, ?_, ?_⟩
  · exact isCompact_range k.continuous
  · apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      k.isoOpensRange.hom _).mp
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hkq]
    exact hgeo
  · let α := pullback.map (pullback.snd h A) (B.toScheme.fromSpecResidueField s₁)
        h (S.fromSpecResidueField (A s₁)) (pullback.fst h A)
        (Spec.map (A.residueFieldMap s₁)) A (pullback.condition).symm
        (A.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
        eqToHom (congrArg h.fiber hs)
    have hα : α ≫ h.fiberι (b s₀) =
        (pullback.snd h A).fiberι s₁ ≫ pullback.fst h A := by
      dsimp only [α]
      rw [Category.assoc, fiberι_eqToHom h hs]
      simp [Scheme.Hom.fiberι]
    ext z
    let x := (pullback.snd h A).fiberι s₁ z
    have hx : pullback.snd h A x = s₁ :=
      ((pullback.snd h A).range_fiberι s₁).le ⟨z, rfl⟩
    have hxq : q (L x) = u₀ := by
      rw [← Scheme.Hom.comp_apply, hLq, Scheme.Hom.comp_apply, hx]
      rfl
    change x ∈ Set.range k ↔ α z ∈ T
    rw [hrange_k, hrange_u _ hxq, ← hT]
    change pullback.fst h A₀ (L x) ∈ Set.range j ↔
      h.fiberι (b s₀) (α z) ∈ Set.range j
    have he₁ := congrArg (fun t ↦ t x) hLfst
    have he₂ := congrArg (fun t ↦ t z) hα
    exact iff_of_eq (congrArg (fun y ↦ y ∈ Set.range j) (he₁.trans he₂.symm))

end AlgebraicGeometry
