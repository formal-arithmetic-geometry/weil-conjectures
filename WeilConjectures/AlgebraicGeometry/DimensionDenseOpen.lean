/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dense open subschemes of schemes of finite type over a field

A dense open subscheme `U` of a quasi-compact scheme `Z` locally of finite type over a field has
the same dimension as `Z`. The proof reduces to the integral case
(`AlgebraicGeometry.topologicalKrullDim_opens_eq`) by endowing the closure of the generic point of
each irreducible component of `Z` with the structure of an integral closed subscheme: the
scheme-theoretic image of the spectrum of its residue field.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isReduced_image`: the scheme-theoretic image of a quasi-compact
  morphism from a reduced scheme is reduced.
- `AlgebraicGeometry.exists_isIntegral_isClosedImmersion_range_eq_closure`: the closure of a point
  of a quasi-separated scheme underlies an integral closed subscheme.
- `IsOpen.mem_of_dense_of_forall_specializes_eq`: a dense open subset of a noetherian quasi-sober
  `T₀` space contains the generic points of all irreducible components.
- `AlgebraicGeometry.topologicalKrullDim_le_of_dense`: `dim Z ≤ dim U` for a dense open `U`.
-/

@[expose] public section

universe u

open CategoryTheory Topology Order

/-- In a noetherian quasi-sober `T₀` space, a dense open subset `U` contains every maximal point
`η` (a point without proper generalization, i.e. the generic point of an irreducible component):
`U` meets the open complement of the closures of the finitely many other maximal points, and any
point there is a specialization of `η`. -/
theorem IsOpen.mem_of_dense_of_forall_specializes_eq {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [TopologicalSpace.NoetherianSpace X] {U : Set X} (hU : IsOpen U)
    (hd : Dense U) {η : X} (hη : ∀ y, y ⤳ η → y = η) : η ∈ U := by
  set M := {ξ | ξ ∈ (Set.univ : Set X) ∧ ∀ z ∈ (Set.univ : Set X), z ⤳ ξ → z = ξ}
  have hM : (M \ {η}).Finite := (isClosed_univ.finite_setOf_maximal_specializes).sdiff
  let F := ⋃ ξ ∈ M \ {η}, closure ({ξ} : Set X)
  have hF : IsClosed F := hM.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hηF : η ∉ F := by
    simp only [F, Set.mem_iUnion, not_exists]
    intro ξ hξ hηξ
    exact hξ.2 (hη ξ (specializes_iff_mem_closure.mpr hηξ))
  obtain ⟨u, huF, huU⟩ := hd.inter_open_nonempty _ hF.isOpen_compl ⟨η, hηF⟩
  obtain ⟨ξ, -, hξ, hξu⟩ := isClosed_univ.exists_maximal_specializes (Set.mem_univ u)
  obtain rfl : ξ = η := by
    by_contra hne
    exact huF (Set.mem_biUnion (x := ξ) ⟨⟨Set.mem_univ ξ, hξ⟩, hne⟩
      (specializes_iff_mem_closure.mp hξu))
  exact hξu.mem_open hU huU

namespace AlgebraicGeometry

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced:
the sections of the image inject into the sections of the source. -/
theorem Scheme.Hom.isReduced_image {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [IsReduced X] : IsReduced f.image := by
  refine ⟨fun V ↦ ⟨fun s hs ↦ f.image.IsSheaf.section_ext fun x hx ↦ ?_⟩⟩
  obtain ⟨U, hU, hUV⟩ := f.imageι.isEmbedding.isInducing.isOpen_iff.mp V.2
  obtain rfl : f.imageι ⁻¹ᵁ (⟨U, hU⟩ : Y.Opens) = V := TopologicalSpace.Opens.ext hUV
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := f.imageι x) hx hU
  refine ⟨f.imageι ⁻¹ᵁ W, fun y hy ↦ hWU hy, hxW, ?_⟩
  have := isReduced_of_injective _ (f.toImage_app_injective ⟨W, hW⟩)
  rw [map_zero]
  exact (hs.map _).eq_zero

/-- The closure of a point `z` of a quasi-separated scheme `Z` underlies an integral closed
subscheme: the scheme-theoretic image of `Spec κ(z) ⟶ Z`. -/
theorem exists_isIntegral_isClosedImmersion_range_eq_closure {Z : Scheme.{u}}
    [QuasiSeparatedSpace Z] (z : Z) :
    ∃ (W : Scheme.{u}) (ι : W ⟶ Z), IsIntegral W ∧ IsClosedImmersion ι ∧
      Set.range ι = closure {z} := by
  let f := Z.fromSpecResidueField z
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← f.toImage.denseRange.closure_range,
      ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _
      f.toImage.continuous.continuousOn).closure
  have := f.isReduced_image
  refine ⟨f.image, f.imageι, isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField]

/-- A dense open subscheme `U` of a quasi-compact scheme `Z` locally of finite type over a field
has at least the dimension of `Z`. Every point of `Z` specializes from the generic point `η` of an
irreducible component; `η` lies in `U`, and `U` meets the integral closed subscheme with
underlying set `closure {η}` in a nonempty open subscheme, which has the full dimension of the
closure (`AlgebraicGeometry.topologicalKrullDim_opens_eq`). -/
theorem topologicalKrullDim_le_of_dense {k : Type u} [Field k] {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s] [CompactSpace Z] (U : Z.Opens)
    (hU : Dense (U : Set Z)) : topologicalKrullDim Z ≤ topologicalKrullDim U := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian Z := {}
  let := specializationOrder Z
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, krullDim_eq_iSup_height]
  refine iSup_le fun x ↦ ?_
  obtain ⟨η, -, hη, hηx⟩ := isClosed_univ.exists_maximal_specializes (Set.mem_univ x)
  have hηU : η ∈ U :=
    U.isOpen.mem_of_dense_of_forall_specializes_eq hU fun y hy ↦ hη y (Set.mem_univ y) hy
  refine (WithBot.coe_le_coe.mpr ((height_mono : Monotone (height : Z → ℕ∞)) hηx)).trans ?_
  rw [← topologicalKrullDim_closure_singleton]
  obtain ⟨W, ι, hW, hι, hrange⟩ := exists_isIntegral_isClosedImmersion_range_eq_closure η
  rw [← hrange, ← ι.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range]
  obtain ⟨w, hw⟩ : η ∈ Set.range ι := hrange ▸ subset_closure rfl
  have : Nonempty (ι ⁻¹ᵁ U) := ⟨⟨w, by simpa [hw] using hηU⟩⟩
  rw [← topologicalKrullDim_opens_eq (ι ≫ s) (ι ⁻¹ᵁ U)]
  refine IsInducing.topologicalKrullDim_le (f := fun p : ι ⁻¹ᵁ U ↦ (⟨ι p.1, p.2⟩ : U))
    (.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val ?_)
  exact ι.isClosedEmbedding.isInducing.comp IsInducing.subtypeVal

end AlgebraicGeometry
