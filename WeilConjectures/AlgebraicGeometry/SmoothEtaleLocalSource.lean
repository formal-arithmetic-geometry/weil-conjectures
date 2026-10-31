/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness is étale local on the source

Source: Stacks Project, `descent.tex`, Tag 036U, lemma-smooth-smooth-local-source,
and `morphisms.tex`, Tag 01UA (blueprint: lem-trf-etale-source-smoothness).

## Main statements

- `smooth_iff_of_jointly_surjective_etale`: descent along any jointly surjective étale family.
- `smooth_at_iff_of_etale`: smoothness on an open neighbourhood is invariant under étale
  precomposition at a point, with no finite-presentation assumption on the original morphism.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace AlgebraicGeometry

private theorem smooth_on_range_of_etale
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) [Etale h]
    [Smooth (h ≫ f)] :
    Smooth (Scheme.Opens.ι (⟨Set.range h, h.isOpenMap.isOpen_range⟩ : X.Opens) ≫ f) := by
  let V : X.Opens := ⟨Set.range h, h.isOpenMap.isOpen_range⟩
  change Smooth (V.ι ≫ f)
  let q : U ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι h (by rw [Scheme.Opens.range_ι]; exact Set.Subset.rfl)
  have hq : q ≫ V.ι = h := IsOpenImmersion.lift_fac _ _ _
  have : Etale q := by
    have : Etale (q ≫ V.ι) := hq.symm ▸ inferInstance
    exact Etale.of_comp q V.ι
  have : Surjective q := by
    constructor
    intro z
    obtain ⟨y, hy⟩ := z.property
    refine ⟨y, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hq]
    exact hy
  have : Smooth (q ≫ (V.ι ≫ f)) := by
    rw [← Category.assoc, hq]
    infer_instance
  exact Smooth.of_comp_of_flat_of_surjective q (V.ι ≫ f)

/-- Smoothness is equivalent to smoothness after a jointly surjective étale source family.
The index type may be empty; joint surjectivity then forces the source to be empty.
Source: Stacks Project, `descent.tex`, Tag 036U, lemma-smooth-smooth-local-source
(blueprint: lem-trf-etale-source-smoothness).

Proof:
1. Every `h i` is smooth by `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
   If `f` is smooth, `lem-trf-smooth-composition` makes every `h i ≫ f` smooth.
2. Conversely, étale maps are flat and locally of finite presentation
   (`def-weil-etale-morphism`), so their images `W i` are open by
   `lem-weil-pbc-flat-lfp-open`. Joint surjectivity says that the `W i` cover `X`.
   By `lem-weil-pbc-morphism-factors-through-open-subscheme`, factor `h i` through
   `q i : U i ⟶ (W i).toScheme`. This factor is surjective, flat and locally of
   finite presentation, as restriction to the open image preserves these properties.
   The restriction of `f` is the map of `lem-weil-pbc-smooth-restrict-open-subschemes`
   with target open equal to the whole target. Its composite with `q i` is `h i ≫ f`.
   Thus `lem-sbc-smooth-flat-surjective-source-descent` makes each restriction smooth.
3. Apply `lem-weil-pbc-smooth-local-on-source` to the open cover `W i` to conclude.
   No separatedness, quasi-compactness or Noetherian assumption is used. -/
theorem smooth_iff_of_jointly_surjective_etale
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v} (U : I → Scheme.{u})
    (h : ∀ i : I, U i ⟶ X) [∀ i : I, Etale (h i)]
    (hcover : ∀ x : X, ∃ (i : I) (y : U i), h i y = x) :
    Smooth f ↔ ∀ i : I, Smooth (h i ≫ f) := by
  constructor
  · intro hf i
    have : Smooth f := hf
    infer_instance
  · intro hf
    let V : I → X.Opens := fun i ↦ ⟨Set.range (h i), (h i).isOpenMap.isOpen_range⟩
    have hV : iSup V = ⊤ := by
      apply top_le_iff.mp
      intro x _
      obtain ⟨i, y, hy⟩ := hcover x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) V hV
    intro i
    have : Smooth (h i ≫ f) := hf i
    exact smooth_on_range_of_etale (h i) f

/-- Étale precomposition preserves and detects smoothness at a point. Here smoothness at a
point means smoothness on an open neighbourhood, expressed directly by the two existentials.
Source: Stacks Project, `descent.tex`, Tag 036U, lemma-smooth-smooth-local-source,
and `morphisms.tex`, Tag 01UA (blueprint: lem-trf-etale-source-smoothness).

Proof (the pointwise clause, step 4 of the node):
If `f` is smooth on an open neighbourhood `V` of `h u`, restrict `h` to the inverse
image of `V`. This is étale by `def-weil-etale-morphism`, hence smooth by
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres`. The restriction of `f` is the
map from `lem-weil-pbc-smooth-restrict-open-subschemes`; composition is smooth by
`lem-trf-smooth-composition`, giving a smooth neighbourhood of `u` for `h ≫ f`.
Conversely, suppose `h ≫ f` is smooth on an open neighbourhood `W` of `u`.
The image `h(W)` is open by `lem-weil-pbc-flat-lfp-open` and contains `h u`.
By `lem-weil-pbc-morphism-factors-through-open-subscheme`, the restriction of `h`
factors through this image. This factor is surjective, flat and locally of finite
presentation (`def-weil-etale-morphism`); its composite with the restriction of `f`
is smooth. Apply `lem-sbc-smooth-flat-surjective-source-descent` to get smoothness
of `f` on `h(W)`. No global finite-presentation assumption on `f` is required. -/
theorem smooth_at_iff_of_etale
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) [Etale h] (u : U) :
    (∃ V : X.Opens, h u ∈ V ∧ Smooth (V.ι ≫ f)) ↔
      ∃ W : U.Opens, u ∈ W ∧ Smooth (W.ι ≫ h ≫ f) := by
  constructor
  · rintro ⟨V, hu, hV⟩
    refine ⟨h ⁻¹ᵁ V, hu, ?_⟩
    have : Smooth (V.ι ≫ f) := hV
    rw [← morphismRestrict_ι_assoc]
    infer_instance
  · rintro ⟨W, hu, hW⟩
    let g := W.ι ≫ h
    have : Etale g := by dsimp [g]; infer_instance
    have : Smooth (g ≫ f) := by simpa only [g, Category.assoc] using hW
    refine ⟨⟨Set.range g, g.isOpenMap.isOpen_range⟩, ?_, smooth_on_range_of_etale g f⟩
    exact ⟨⟨u, hu⟩, rfl⟩

end AlgebraicGeometry
