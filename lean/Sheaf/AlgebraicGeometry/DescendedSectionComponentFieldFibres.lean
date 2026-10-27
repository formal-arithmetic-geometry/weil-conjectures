module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Field fibres of a descended section component

Source: Stacks Project, More on Morphisms, Tag 057I, `lemma-descent-connected-fibres`,
final fibre assertion; Varieties, Tag 04KV, rational-point criterion.
(blueprint: lem-trf-descended-section-component-field-fibres)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem preimage_component_range {A D : Type*}
    [TopologicalSpace A] [TopologicalSpace D] (j : A → D)
    (hj : Topology.IsEmbedding j) (x : A) :
    j ⁻¹' connectedComponentIn (Set.range j) (j x) = connectedComponent x := by
  have hr : connectedComponentIn (Set.range j) (j x) ⊆ Set.range j :=
    connectedComponentIn_subset _ _
  have hi : j '' (j ⁻¹' connectedComponentIn (Set.range j) (j x)) =
      connectedComponentIn (Set.range j) (j x) := Set.image_preimage_eq_of_subset hr
  apply Set.Subset.antisymm
  · apply IsPreconnected.subset_connectedComponent
    · apply hj.isInducing.isPreconnected_image.mp
      rw [hi]
      exact isPreconnected_connectedComponentIn
    · exact mem_connectedComponentIn ⟨x, rfl⟩
  · intro y hy
    exact (isPreconnected_connectedComponent.image j hj.continuous.continuousOn
      |>.subset_connectedComponentIn ⟨x, mem_connectedComponent, rfl⟩
        (Set.image_subset_range _ _)) ⟨y, hy, rfl⟩

/-- The canonical residue-field fibre comparison identifies the descended open with the
component of the rational section point. This open is geometrically connected. If the
original fibre is geometrically connected, both the extended open and the original fibre
open are the whole fibre. Opens are recorded by their underlying open subsets, which
uniquely specify their open subschemes.

Source: Stacks Project, Tag 057I, `lemma-descent-connected-fibres`, final fibre assertion,
and Tag 04KV, `lemma-geometrically-connected-if-connected-and-point`.
Proof:
1. Apply `lem-weil-pbc-fibre-of-base-change` to the pullback of `f` along `p`. Its
   cartesian residue-field square gives the isomorphism `e`, characterized by the two
   projection equations below. Since `C` is the inverse image of `U`, the pullbacks of
   these opens coincide under `e` by the open-immersion universal property.
2. Base change the section to `Spec κ(t)`. This gives `q`, with the two displayed
   projection equations. The fibre-component hypothesis identifies the pulled-back
   open with the connected component of its rational point. That component is connected
   and contains this point, so `lem-sbc-connected-rational-point-geometrically-connected`
   makes the open geometrically connected. Transport this along `e`.
3. If the original fibre is geometrically connected, its extension to `κ(t)` is
   connected. The component containing the section point is then the whole fibre.
4. The extension projection is surjective: use `lem-pc-field-extension-surjective`
   and `lem-weil-pbc-surjective-base-change`. Therefore an open whose inverse image is
   the whole extended fibre is itself the whole original fibre.
No flatness or geometric reducedness is used.
(blueprint: lem-trf-descended-section-component-field-fibres) -/
theorem descended_section_component_field_fibres
    {X B T : Scheme.{u}} (f : X ⟶ B) [LocallyOfFiniteType f]
    (p : T ⟶ B) [Surjective p] (σ : T ⟶ X) (hσ : σ ≫ f = p)
    (C : (pullback f p).Opens)
    (hC : ∀ t : T, (C : Set ↥(pullback f p)) ∩ (pullback.snd f p) ⁻¹' {t} =
      connectedComponentIn ((pullback.snd f p) ⁻¹' {t})
        ((pullback.lift σ (𝟙 T) (hσ.trans (Category.id_comp p).symm)) t))
    (U : X.Opens) (hU : (pullback.fst f p) ⁻¹ᵁ U = C) (t : T) :
    ∃ (e : (pullback.snd f p).fiber t ≅
        pullback (f.fiberToSpecResidueField (p t)) (Spec.map (p.residueFieldMap t)))
      (q : Spec (T.residueField t) ⟶ (pullback.snd f p).fiber t),
      e.hom ≫ pullback.fst _ _ ≫ f.fiberι (p t) =
        (pullback.snd f p).fiberι t ≫ pullback.fst f p ∧
      e.hom ≫ pullback.snd _ _ = (pullback.snd f p).fiberToSpecResidueField t ∧
      q ≫ (pullback.snd f p).fiberι t = T.fromSpecResidueField t ≫
        pullback.lift σ (𝟙 T) (hσ.trans (Category.id_comp p).symm) ∧
      q ≫ (pullback.snd f p).fiberToSpecResidueField t = 𝟙 _ ∧
      e.hom ⁻¹ᵁ ((pullback.fst (f.fiberToSpecResidueField (p t))
        (Spec.map (p.residueFieldMap t))) ⁻¹ᵁ ((f.fiberι (p t)) ⁻¹ᵁ U)) =
        ((pullback.snd f p).fiberι t) ⁻¹ᵁ C ∧
      ((((pullback.snd f p).fiberι t) ⁻¹ᵁ C) :
        Set ↥((pullback.snd f p).fiber t)) = connectedComponent (q default) ∧
      GeometricallyConnected
        (((pullback.fst (f.fiberToSpecResidueField (p t))
          (Spec.map (p.residueFieldMap t))) ⁻¹ᵁ ((f.fiberι (p t)) ⁻¹ᵁ U)).ι ≫
          pullback.snd (f.fiberToSpecResidueField (p t)) (Spec.map (p.residueFieldMap t))) ∧
      (GeometricallyConnected (f.fiberToSpecResidueField (p t)) →
        (pullback.fst (f.fiberToSpecResidueField (p t))
          (Spec.map (p.residueFieldMap t))) ⁻¹ᵁ ((f.fiberι (p t)) ⁻¹ᵁ U) = ⊤ ∧
        (f.fiberι (p t)) ⁻¹ᵁ U = ⊤) := by
  let g := pullback.snd f p
  let s : T ⟶ pullback f p :=
    pullback.lift σ (𝟙 T) (hσ.trans (Category.id_comp p).symm)
  have hs : s ≫ g = 𝟙 T := pullback.lift_snd ..
  let hc := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f p) t
  let e := hc.isoPullback
  have he₁ : e.hom ≫ pullback.fst _ _ ≫ f.fiberι (p t) =
      g.fiberι t ≫ pullback.fst f p := by
    rw [hc.isoPullback_hom_fst_assoc]
    exact pullback.lift_fst ..
  have he₂ : e.hom ≫ pullback.snd _ _ = g.fiberToSpecResidueField t :=
    hc.isoPullback_hom_snd
  let q : Spec (T.residueField t) ⟶ g.fiber t :=
    pullback.lift (T.fromSpecResidueField t ≫ s) (𝟙 _)
      (by simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have hq₁ : q ≫ g.fiberι t = T.fromSpecResidueField t ≫ s := pullback.lift_fst ..
  have hq₂ : q ≫ g.fiberToSpecResidueField t = 𝟙 _ := pullback.lift_snd ..
  have hpoint : g.fiberι t (q default) = s t := by
    rw [← Scheme.Hom.comp_apply, hq₁, Scheme.Hom.comp_apply]
    simp
  let V := (g.fiberι t) ⁻¹ᵁ C
  let W := (pullback.fst (f.fiberToSpecResidueField (p t))
    (Spec.map (p.residueFieldMap t))) ⁻¹ᵁ ((f.fiberι (p t)) ⁻¹ᵁ U)
  have hopen : e.hom ⁻¹ᵁ W = V := by
    dsimp [W, V]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Category.assoc, he₁,
      Scheme.Hom.comp_preimage, hU]
  have hcomp : (V : Set ↥(g.fiber t)) = connectedComponent (q default) := by
    have ht := congrArg (fun Z : Set ↥(pullback f p) ↦ (g.fiberι t) ⁻¹' Z) (hC t)
    have hr : (g.fiberι t) ⁻¹' (g ⁻¹' {t}) = Set.univ := by
      rw [← g.range_fiberι t]
      exact Set.preimage_range _
    have hv : (V : Set ↥(g.fiber t)) =
        (g.fiberι t) ⁻¹' connectedComponentIn (g ⁻¹' {t}) (s t) := by
      change (V : Set ↥(g.fiber t)) ∩ ((g.fiberι t) ⁻¹' (g ⁻¹' {t})) =
        (g.fiberι t) ⁻¹' connectedComponentIn (g ⁻¹' {t}) (s t) at ht
      simpa only [hr, Set.inter_univ] using ht
    rw [hv, ← g.range_fiberι t, ← hpoint]
    exact preimage_component_range _ (g.fiberι t).isEmbedding _
  have hconnV : _root_.IsConnected (V : Set ↥(g.fiber t)) := by
    rw [hcomp]
    exact isConnected_connectedComponent
  have hconnW : _root_.IsConnected (W : Set ↥(pullback
      (f.fiberToSpecResidueField (p t)) (Spec.map (p.residueFieldMap t)))) := by
    apply e.hom.homeomorph.isConnected_preimage.mp
    change _root_.IsConnected (SetLike.coe (e.hom ⁻¹ᵁ W))
    rw [hopen]
    exact hconnV
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hconnW
  have hqW : Set.range (q ≫ e.hom) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    have ha : a = default := Subsingleton.elim _ _
    subst a
    change e.hom (q default) ∈ W
    change q default ∈ e.hom ⁻¹ᵁ W
    rw [hopen]
    change q default ∈ (V : Set ↥(g.fiber t))
    rw [hcomp]
    exact mem_connectedComponent
  let r := IsOpenImmersion.lift W.ι (q ≫ e.hom) hqW
  have hgeom : GeometricallyConnected
      (W.ι ≫ pullback.snd (f.fiberToSpecResidueField (p t))
        (Spec.map (p.residueFieldMap t))) := by
    apply GeometricallyConnected.of_connectedSpace_of_section _ r
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, he₂, hq₂]
    rfl
  refine ⟨e, q, he₁, he₂, hq₁, hq₂, hopen, hcomp, hgeom, ?_⟩
  intro hgeomF
  have : GeometricallyConnected (f.fiberToSpecResidueField (p t)) := hgeomF
  have : GeometricallyConnected (pullback.snd (f.fiberToSpecResidueField (p t))
      (Spec.map (p.residueFieldMap t))) := inferInstance
  have : ConnectedSpace ↥(pullback (f.fiberToSpecResidueField (p t))
      (Spec.map (p.residueFieldMap t))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd _ _)
  have : ConnectedSpace ↥(g.fiber t) :=
    e.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  have hVtop : V = ⊤ := by
    apply TopologicalSpace.Opens.ext
    exact hcomp.trans (PreconnectedSpace.connectedComponent_eq_univ _)
  have hWtop : W = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := e.hom.surjective x
    have hy : y ∈ e.hom ⁻¹ᵁ W := by
      rw [hopen, hVtop]
      trivial
    exact hy
  refine ⟨hWtop, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := (pullback.fst (f.fiberToSpecResidueField (p t))
    (Spec.map (p.residueFieldMap t))).surjective x
  have hy : y ∈ W := by
    rw [hWtop]
    trivial
  exact hy

end AlgebraicGeometry
