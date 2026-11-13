/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.AlgebraicGeometry.Properties

/-! # Spectral presentation of intersections of quasi-compact opens

## References

* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 094L](https://stacks.math.columbia.edu/tag/094L)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The distinct original opens contained in the chosen member, ordered by reverse inclusion. -/
abbrev qcOpenIntersectionIndex {X : Scheme.{u}} {I : Type v} (U : I → X.Opens) (i₀ : I) :=
  OrderDual {V : X.Opens // V ∈ Set.range U ∧ V ≤ U i₀}

/-- The inclusion diagram on the opposite of the reverse-inclusion index. -/
def qcOpenIntersectionDiagram {X : Scheme.{u}} {I : Type v} (U : I → X.Opens) (i₀ : I) :
    (qcOpenIntersectionIndex U i₀)ᵒᵖ ⥤ TopCat.{u} where
  obj V := TopCat.of V.unop.val
  map f := (Opens.toTopCat X.toTopCat).map (homOfLE (leOfHom f.unop))

/-- The cone of literal inclusions from the subspace intersection, without a scheme structure
on the intersection. -/
def qcOpenIntersectionCone {X : Scheme.{u}} {I : Type v} (U : I → X.Opens) (i₀ : I) :
    Cone (qcOpenIntersectionDiagram U i₀) where
  pt := TopCat.of {x : X // ∀ i : I, x ∈ U i}
  π :=
    { app := fun (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) ↦ (TopCat.ofHom
        ⟨fun (x : {x : X // ∀ i : I, x ∈ U i}) ↦ ⟨x.val, by
          obtain ⟨i, hi⟩ := V.unop.property.1
          exact hi ▸ x.property i⟩,
          continuous_subtype_val.subtype_mk _⟩ :
          TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶ TopCat.of V.unop.val)
      naturality := fun _ _ _ ↦ rfl }

/-- Cofinal spectral presentation of a directed intersection of quasi-compact opens in a
quasi-separated scheme: the opens below `U i₀` form a small directed cofinal index with the same
intersection, each is spectral, the inclusions are spectral maps, and the subspace intersection
is the limit of the inclusion diagram. -/
theorem qcOpenIntersection_spectral_presentation (X : Scheme.{u}) [QuasiSeparatedSpace X]
    {I : Type v} [Nonempty I] (U : I → X.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) (i₀ : I) :
    Small.{u} (qcOpenIntersectionIndex U i₀) ∧
    Nonempty (qcOpenIntersectionIndex U i₀) ∧
    IsDirected (qcOpenIntersectionIndex U i₀) (· ≤ ·) ∧
    IsLeast (α := qcOpenIntersectionIndex U i₀) Set.univ
      (⟨U i₀, ⟨⟨i₀, rfl⟩, le_rfl⟩⟩ : qcOpenIntersectionIndex U i₀) ∧
    (∀ i : I, ∃ V : qcOpenIntersectionIndex U i₀, V.val ≤ U i) ∧
    (⋂ i : I, (U i : Set X)) = ⋂ V : qcOpenIntersectionIndex U i₀, (V.val : Set X) ∧
    (∀ V : qcOpenIntersectionIndex U i₀,
      QuasiSeparatedSpace V.val.toScheme ∧ SpectralSpace V.val.toScheme) ∧
    (∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
      IsSpectralMap ((qcOpenIntersectionDiagram U i₀).map f)) ∧
    Nonempty (IsLimit (qcOpenIntersectionCone U i₀)) ∧
    (∀ t : (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) →
        (qcOpenIntersectionDiagram U i₀).obj V,
      (∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
        (qcOpenIntersectionDiagram U i₀).map f (t V) = t W) →
      ∃! x : (qcOpenIntersectionCone U i₀).pt,
        ∀ V : (qcOpenIntersectionIndex U i₀)ᵒᵖ,
          (qcOpenIntersectionCone U i₀).π.app V x = t V) ∧
    (inferInstance : TopologicalSpace (qcOpenIntersectionCone U i₀).pt) =
      ⨅ V : (qcOpenIntersectionIndex U i₀)ᵒᵖ,
        TopologicalSpace.induced ((qcOpenIntersectionCone U i₀).π.app V)
          (inferInstance : TopologicalSpace ((qcOpenIntersectionDiagram U i₀).obj V)) := by
  classical
  let B : qcOpenIntersectionIndex U i₀ := ⟨U i₀, ⟨⟨i₀, rfl⟩, le_rfl⟩⟩
  have hcof (i : I) : ∃ V : qcOpenIntersectionIndex U i₀, V.val ≤ U i := by
    obtain ⟨k, hk⟩ := hdir i i₀
    exact ⟨⟨U k, ⟨⟨k, rfl⟩, hk.trans inf_le_right⟩⟩, hk.trans inf_le_left⟩
  have hcompact (V : qcOpenIntersectionIndex U i₀) : IsCompact (V.val : Set X) := by
    obtain ⟨i, hi⟩ := V.property.1
    exact hi ▸ hU i
  have hcommon
      (t : (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) →
        (qcOpenIntersectionDiagram U i₀).obj V)
      (ht : ∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
        (qcOpenIntersectionDiagram U i₀).map f (t V) = t W)
      (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) :
      (t V).val = (t (op B)).val := by
    exact congrArg Subtype.val (ht V (op B)
      (homOfLE (show B ≤ V.unop from V.unop.property.2)).op)
  have hpoint
      (t : (V : (qcOpenIntersectionIndex U i₀)ᵒᵖ) →
        (qcOpenIntersectionDiagram U i₀).obj V)
      (ht : ∀ (V W : (qcOpenIntersectionIndex U i₀)ᵒᵖ) (f : V ⟶ W),
        (qcOpenIntersectionDiagram U i₀).map f (t V) = t W) :
      ∀ i : I, (t (op B)).val ∈ U i := by
    intro i
    obtain ⟨V, hV⟩ := hcof i
    exact hV (hcommon t ht (op V) ▸ (t (op V)).property)
  refine ⟨inferInstance, ⟨B⟩, ?_, ⟨Set.mem_univ _, ?_⟩, hcof, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    intro V W
    obtain ⟨i, hi⟩ := V.property.1
    obtain ⟨j, hj⟩ := W.property.1
    obtain ⟨k, hk⟩ := hdir i j
    have hkV : U k ≤ V.val := hi ▸ hk.trans inf_le_left
    have hkW : U k ≤ W.val := hj ▸ hk.trans inf_le_right
    exact ⟨⟨U k, ⟨⟨k, rfl⟩, hkV.trans V.property.2⟩⟩, hkV, hkW⟩
  · intro V _
    exact V.property.2
  · ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hx V
      obtain ⟨i, hi⟩ := V.property.1
      exact hi ▸ hx i
    · intro hx i
      obtain ⟨V, hV⟩ := hcof i
      exact hV (hx V)
  · intro V
    have : QuasiSeparatedSpace V.val.toScheme :=
      V.val.isOpenEmbedding'.quasiSeparatedSpace
    have : CompactSpace V.val.toScheme := isCompact_iff_compactSpace.mp (hcompact V)
    exact ⟨inferInstance, {}⟩
  · intro V W f
    let g : V.unop.val → W.unop.val := Set.inclusion (leOfHom f.unop)
    have hg : Topology.IsOpenEmbedding g := Opens.isOpenEmbedding_of_le (leOfHom f.unop)
    have : CompactSpace (V.unop.val : Set X) :=
      isCompact_iff_compactSpace.mp (hcompact V.unop)
    have : QuasiSeparatedSpace (W.unop.val : Set X) :=
      W.unop.val.isOpenEmbedding'.quasiSeparatedSpace
    change IsSpectralMap g
    refine ⟨hg.continuous, ?_⟩
    intro K hKopen hKcompact
    rw [hg.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range]
    exact hKcompact.inter_of_isOpen (isCompact_range hg.continuous)
      hKopen hg.isOpen_range
  · refine ⟨{
      lift := fun s ↦ TopCat.ofHom (
        ⟨fun x ↦ ⟨(s.π.app (op B) x).val,
          hpoint (fun V ↦ s.π.app V x) (fun V W f ↦ by
            exact ConcreteCategory.congr_hom (s.w f) x)⟩,
          (continuous_subtype_val.comp (s.π.app (op B)).hom.continuous).subtype_mk _⟩)
      fac := ?_
      uniq := ?_ }⟩
    · intro s V
      ext x
      apply Subtype.ext
      exact (hcommon (fun W ↦ s.π.app W x) (fun V W f ↦
        ConcreteCategory.congr_hom (s.w f) x) V).symm
    · intro s m hm
      ext x
      apply Subtype.ext
      exact congrArg
        (fun y : (qcOpenIntersectionDiagram U i₀).obj (op B) ↦ y.val)
        (ConcreteCategory.congr_hom (hm (op B)) x)
  · intro t ht
    refine ⟨⟨(t (op B)).val, hpoint t ht⟩, ?_, ?_⟩
    · intro V
      exact Subtype.ext (hcommon t ht V).symm
    · intro x hx
      apply Subtype.ext
      exact congrArg (fun y : (qcOpenIntersectionDiagram U i₀).obj (op B) ↦ y.val)
        (hx (op B))
  · apply le_antisymm
    · apply le_iInf
      intro V
      exact (qcOpenIntersectionCone U i₀).π.app V |>.hom.continuous.le_induced
    · apply (iInf_le _ (op B)).trans
      change TopologicalSpace.induced
        (fun x : {x : X // ∀ i, x ∈ U i} ↦
          (⟨x.val, x.property i₀⟩ : U i₀))
        (TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace X)) ≤ _
      rw [induced_compose]
      exact le_rfl

end AlgebraicGeometry.Scheme
