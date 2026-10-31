/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Topology.FilteredSpectrumTopologicalLimit
import WeilConjectures.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare

/-! # Topology of a directed quasi-affine chart limit

Source: Stacks Project, Tag 0API, `more-groupoids.tex`, proof of
`lemma-sits-in-functions`, middle paragraph and final cartesian squares.
(blueprint: lem-a1-quasi-affine-chart-limit-topology)
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The actual restriction-ring diagram of a decreasing family of open subschemes.
Its objects are the global sections of the open subschemes, and its arrows are
pullback of global sections along their canonical inclusions.

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`, the system of rings `A_i`.
(blueprint: lem-a1-quasi-affine-chart-limit-topology) -/
def quasiAffineChartSectionDiagram (Y : Scheme.{u})
    {I : Type u} [PartialOrder I] (U : I → Y.Opens) (hU : Antitone U) :
    I ⥤ CommRingCat.{u} :=
  ({ obj := fun i ↦ op (U i)
     map := fun f ↦ (homOfLE (hU f.le)).op } : I ⥤ Y.Opensᵒᵖ) ⋙
    Y.restrictFunctor.op ⋙ (Over.forget Y).op ⋙ Scheme.Γ

/-- The intersection of decreasing quasi-affine open charts has its subspace topology
inside the spectrum of the colimit ring. The image is the intersection of the
quasi-compact chart inverse images, and every ambient open contained in all charts
has exactly its indicated inverse-image description, without a compactness condition.

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`, middle paragraph and
final cartesian squares (blueprint: lem-a1-quasi-affine-chart-limit-topology).

Proof:
1. The canonical quasi-affine embedding lemma makes each `toSpecΓ` an open immersion
   with quasi-compact image. Naturality of the affine adjunction identifies its
   composites with the transition maps with its restriction from an earlier chart
   (lem-trf-quasi-affine-canonical-affine-embedding,
   lem-a1-locally-ringed-space-affine-adjunction, def-weil-open-immersion).
2. The compatible-family homeomorphism for the filtered spectrum colimit gives a
   continuous map from the intersection, uniquely determined by its coordinates
   (lem-a1-filtered-spectrum-topological-limit).
3. A point in every chart inverse image lifts uniquely to a point in each chart.
   Injectivity of the canonical embeddings and a common upper bound identify these
   points in `Y`. Nonemptiness of the index set gives a common point in the
   intersection. This proves the range formula and injectivity of the map.
4. Fix one chart. Its inverse embedding composed with the spectrum projection is
   continuous into `Y`, hence into the intersection with its subspace topology.
   This gives the embedding assertion. The final clause of the filtered-spectrum
   lemma gives compactness of each open chart inverse image.
5. For an ambient open `W` contained in every chart, the affinization square of
   each later chart inclusion is cartesian. Inside this square the inverse image
   of the earlier image of `W` is its later image, with the same point of `W`
   (lem-a1-quasi-affine-open-affinization-square, def-weil-open-immersion).
6. One inclusion in the image formula follows from the coordinates. For the other,
   lift a point of the spectrum inverse image to `w` in `W` at the fixed chart.
   Step 5 identifies every later coordinate with the image of `w`. Common upper
   bounds and naturality identify all remaining coordinates. Coordinate uniqueness
   gives that point as `t(w)`. The formula is open by continuity of the projection
   and openness of the chart embedding. Compactness of `W` is never used. -/
theorem quasiAffineChartLimitTopology
    (Y : Scheme.{u}) (I : Type u) [PartialOrder I] [Nonempty I]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (U : I → Y.Opens) (hU : Antitone U)
    [hqa : ∀ i : I, (U i).toScheme.IsQuasiAffine]
    (c : Cocone (quasiAffineChartSectionDiagram Y U hU)) (hc : IsColimit c) :
    ∃ t : C({x : Y // ∀ i : I, x ∈ U i}, Spec c.pt),
      (∀ (i : I) (x : {x : Y // ∀ i : I, x ∈ U i}),
        (Spec.map (c.ι.app i)) (t x) = (U i).toScheme.toSpecΓ ⟨x.val, x.property i⟩) ∧
      (∀ t' : C({x : Y // ∀ i : I, x ∈ U i}, Spec c.pt),
        (∀ (i : I) (x : {x : Y // ∀ i : I, x ∈ U i}),
          (Spec.map (c.ι.app i)) (t' x) =
            (U i).toScheme.toSpecΓ ⟨x.val, x.property i⟩) → t' = t) ∧
      Topology.IsEmbedding t ∧
      Set.range t = ⋂ i : I,
        (Spec.map (c.ι.app i)) ⁻¹' Set.range (U i).toScheme.toSpecΓ ∧
      (∀ i : I,
        IsOpen ((Spec.map (c.ι.app i)) ⁻¹' Set.range (U i).toScheme.toSpecΓ) ∧
        IsCompact ((Spec.map (c.ι.app i)) ⁻¹' Set.range (U i).toScheme.toSpecΓ)) ∧
      (∀ W : Y.Opens, (W : Set Y) ⊆ ⋂ i : I, (U i : Set Y) →
        (∀ i : I,
          t '' {x | x.val ∈ W} = (Spec.map (c.ι.app i)) ⁻¹'
            ((U i).toScheme.toSpecΓ '' {x : (U i).toScheme | x.val ∈ W})) ∧
        IsOpen (t '' {x | x.val ∈ W})) := by
  classical
  let F := quasiAffineChartSectionDiagram Y U hU
  let E := {x : Y // ∀ i : I, x ∈ U i}
  let j (i : I) := (U i).toScheme.toSpecΓ
  let p (i : I) := Spec.map (c.ι.app i)
  let inc (i k : I) (h : i ≤ k) := Y.homOfLE (hU h)
  have nat (i k : I) (h : i ≤ k) (x : (U k).toScheme) :
      Spec.map (F.map (homOfLE h)) (j k x) = j i (inc i k h x) := by
    exact (congrArg (fun f : (U k).toScheme ⟶ Spec (F.obj i) => f x)
      (Scheme.toSpecΓ_naturality (inc i k h))).symm
  have compat (i k : I) (h : i ≤ k) (z : Spec c.pt) :
      Spec.map (F.map (homOfLE h)) (p k z) = p i z := by
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map f z) (c.w (homOfLE h))
  obtain ⟨⟨e, he⟩, hcompact⟩ := filteredSpectrumTopologicalLimit I hdir F c hc
  have coord (z : Spec c.pt) (i : I) : (e z).val i = p i z :=
    congrFun (he z) i
  have extpt (z z' : Spec c.pt) (h : ∀ i, p i z = p i z') : z = z' := by
    apply e.injective
    apply Subtype.ext
    funext i
    rw [coord, coord, h i]
  let a : E → {q : (i : I) → Spec (F.obj i) //
      ∀ (i k : I) (h : i ≤ k), Spec.map (F.map (homOfLE h)) (q k) = q i} :=
    fun x => ⟨fun i => j i ⟨x.val, x.property i⟩, fun i k h => by
      rw [nat]
      apply congrArg (j i)
      exact Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have ha : Continuous a := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (j i).continuous.comp (continuous_subtype_val.subtype_mk _)
  let t : C(E, Spec c.pt) := ⟨fun x => e.symm (a x), e.symm.continuous.comp ha⟩
  have ht (i : I) (x : E) : p i (t x) = j i ⟨x.val, x.property i⟩ := by
    rw [← coord]
    exact congrArg (fun q => q.val i) (e.apply_symm_apply (a x))
  refine ⟨t, ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    apply ContinuousMap.ext
    intro x
    exact extpt _ _ (fun i => (ht' i x).trans (ht i x).symm)
  · let i : I := Classical.choice inferInstance
    let v : E → (U i).toScheme := fun x => ⟨x.val, x.property i⟩
    have hv : Topology.IsEmbedding v :=
      (Topology.IsEmbedding.subtypeVal
        (p := fun x : Y => ∀ k : I, x ∈ U k)).codRestrict _ (fun x => x.property i)
    have hemb := (j i).isEmbedding.comp hv
    have heq : (j i) ∘ v = (p i) ∘ t := funext (fun x => (ht i x).symm)
    rw [heq] at hemb
    exact Topology.IsEmbedding.of_comp t.continuous (p i).continuous hemb
  · apply Set.Subset.antisymm
    · rintro z ⟨x, rfl⟩
      exact Set.mem_iInter.mpr (fun i => ⟨⟨x.val, x.property i⟩, (ht i x).symm⟩)
    · intro z hz
      have lifts (i : I) : ∃ x : (U i).toScheme, j i x = p i z :=
        Set.mem_iInter.mp hz i
      choose q hq using lifts
      have coh (i k : I) (h : i ≤ k) : (q i).val = (q k).val := by
        have heq : j i (q i) = j i (inc i k h (q k)) := by
          rw [hq i, ← nat i k h, hq k, compat i k h]
        simpa only [inc, Scheme.homOfLE_apply] using
          congrArg Subtype.val ((j i).isEmbedding.injective heq)
      let i : I := Classical.choice inferInstance
      have all_eq (l : I) : (q i).val = (q l).val := by
        obtain ⟨k, hik, hlk⟩ := hdir i l
        exact (coh i k hik).trans (coh l k hlk).symm
      let x : E := ⟨(q i).val, fun l => (all_eq l).symm ▸ (q l).property⟩
      refine ⟨x, extpt _ _ (fun l => ?_)⟩
      rw [ht, ← hq]
      apply congrArg (j l)
      exact Subtype.ext (all_eq l)
  · intro i
    have ho : IsOpen (Set.range (j i)) := (j i).isOpenEmbedding.isOpenMap.isOpen_range
    exact ⟨ho.preimage (p i).continuous,
      hcompact i _ ho (isCompact_range (j i).continuous)⟩
  · intro W hW
    have hWU (w : Y) (hw : w ∈ W) (i : I) : w ∈ U i :=
      Set.mem_iInter.mp (hW hw) i
    have image_eq (i : I) :
        t '' {x : E | x.val ∈ W} =
          (p i) ⁻¹' (j i '' {x : (U i).toScheme | x.val ∈ W}) := by
      apply Set.Subset.antisymm
      · rintro z ⟨x, hx, rfl⟩
        exact ⟨⟨x.val, x.property i⟩, hx, (ht i x).symm⟩
      · rintro z ⟨w, hw, hwz⟩
        let x : E := ⟨w.val, hWU w.val hw⟩
        refine ⟨x, hw, extpt _ _ (fun l => ?_)⟩
        obtain ⟨k, hik, hlk⟩ := hdir i l
        change i ≤ k at hik
        change l ≤ k at hlk
        let wk : (U k).toScheme := ⟨w.val, hWU w.val hw k⟩
        have hsq := isPullback_toSpecΓ_of_isOpenImmersion (inc i k hik)
        have heq : (Spec.map (inc i k hik).appTop).base (p k z) =
            (inc i k hik ≫ (U i).toScheme.toSpecΓ).base wk := by
          change Spec.map (F.map (homOfLE hik)) (p k z) = j i (inc i k hik wk)
          rw [compat i k hik z, ← hwz]
          apply congrArg (j i)
          apply Subtype.ext
          exact (Scheme.homOfLE_apply (hU hik) wk).symm
        obtain ⟨v, hv, hvw⟩ := exists_preimage_of_isPullback hsq (p k z) wk heq
        have hv' : v = wk := hvw
        have hk : p k z = j k wk := by
          rw [← hv', ← hv]
        rw [ht, ← compat l k hlk z, hk, nat]
        apply congrArg (j l)
        apply Subtype.ext
        exact (Scheme.homOfLE_apply (hU hlk) wk).symm
    refine ⟨image_eq, ?_⟩
    let i : I := Classical.choice inferInstance
    rw [image_eq i]
    exact ((j i).isOpenEmbedding.isOpenMap _ (W.isOpen.preimage continuous_subtype_val)).preimage
      (p i).continuous

end AlgebraicGeometry.Scheme
