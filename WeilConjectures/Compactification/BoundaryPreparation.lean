/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.Defs

/-!

# Boundary preparation for the two-open compactification theorem

This file provides the boundary-preparation inputs of the two-open compactification
theorem, following the blueprint chapter "Nagata compactification", sections
"Separating boundary pieces" and "The two-open compactification theorem"
(proof order items 34, 36 and 37):

- `AlgebraicGeometry.Compactification.denseRefinement`: the scheme-theoretically dense
  refinement of a compactification, replacing the ambient scheme by the
  scheme-theoretic image of the open immersion (blueprint:
  `def:nagata-dense-refinement`, `prop:nagata-dense-refinement`), together with
  `AlgebraicGeometry.HasCompactification.exists_isSchemeTheoreticallyDense`
  (blueprint: `def:nagata-two-open-dense-compactifications`,
  `lemma:nagata-two-open-dense-compactifications`; proof order item 34);
- `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`: the
  **constructible-boundary separation blow-up** (Stacks Project Tags 080P and 0F3V):
  two disjoint constructible closed subsets of a quasi-compact open `U ⊆ X` acquire
  disjoint closures of their inverse images after a `U`-admissible blow-up
  (blueprint: `def:nagata-separate-constructible-closed`,
  `lemma:nagata-separate-constructible-closed`,
  `def:nagata-two-open-prepared-boundaries`; proof order item 36);
- `AlgebraicGeometry.StrictTransform.disjoint_of_disjoint`: disjointness of closed
  subschemes persists along strict transforms of arbitrary modifications (blueprint:
  `lemma:nagata-boundary-disjoint-persists`; proof order item 37).

The proof of `exists_admissibleBlowup_disjoint_closures` combines the boundary
separation theorem `disjoint_range_strictTransformMap_sup` of
`WeilConjectures.Blowup.AdmissibleBlowup` (Stacks Tag 0F3V) with the two range
comparisons proved here: the strict transform of a closed center contains the whole
inverse image of its `U`-part (`mem_range_strictTransformMap`), and is contained in
the full inverse image of the center (`range_strictTransformMap_subset_preimage`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section DenseRefinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The **scheme-theoretically dense refinement** of a compactification of a
quasi-compact morphism: replace the ambient scheme by the scheme-theoretic image of
the open immersion. The refined open immersion is the factor map `c.i.toImage`, an
open immersion because `c.i` is a quasi-compact immersion; the refined proper
morphism is the composite of the image closed immersion with `c.g`.
(Blueprint: `def:nagata-dense-refinement`.) -/
def Compactification.denseRefinement (c : Compactification f) [QuasiCompact f] :
    Compactification f where
  Z := c.i.image
  g := c.i.imageι ≫ c.g
  i := c.i.toImage
  comm := by
    rw [Scheme.Hom.toImage_imageι_assoc]
    exact c.comm
  isProper := inferInstance
  isOpenImmersion := by
    have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
    infer_instance

/-- The dense refinement of a compactification is scheme-theoretically dense: the
factor map through the scheme-theoretic image is scheme-theoretically dominant.
(Blueprint: `prop:nagata-dense-refinement`.) -/
theorem Compactification.denseRefinement_isSchemeTheoreticallyDense
    (c : Compactification f) [QuasiCompact f] :
    c.denseRefinement.IsSchemeTheoreticallyDense := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  change IsSchemeTheoreticallyDominant c.i.toImage
  infer_instance

/-- **Choice of dense compactifications** (blueprint:
`def:nagata-two-open-dense-compactifications`,
`lemma:nagata-two-open-dense-compactifications`; proof order item 34): every
compactifiable quasi-compact morphism admits a scheme-theoretically dense
compactification, namely the dense refinement of any chosen compactification. -/
theorem HasCompactification.exists_isSchemeTheoreticallyDense
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ c : Compactification f, c.IsSchemeTheoreticallyDense :=
  ⟨(HasCompactification.compactification f).denseRefinement,
    (HasCompactification.compactification f).denseRefinement_isSchemeTheoreticallyDense⟩

end DenseRefinement

section StrictTransformRange

variable {X X' Z : Scheme.{u}} (q : Z ⟶ X) (π : X' ⟶ X) (U : X.Opens)

/-- The strict-transform projection and the projection to the source cover the same
morphism to the base. -/
@[reassoc]
lemma strictTransformToSource_comp :
    strictTransformToSource q π U ≫ q = strictTransformMap q π U ≫ π := by
  unfold strictTransformToSource strictTransformMap
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- The strict transform of `q` lies inside the full inverse image of the image of
`q`: the range of the strict-transform projection is contained in `π ⁻¹ (range q)`. -/
theorem range_strictTransformMap_subset_preimage :
    Set.range (strictTransformMap q π U) ⊆ π ⁻¹' (Set.range q) := by
  rintro _ ⟨t, rfl⟩
  refine Set.mem_preimage.mpr ⟨strictTransformToSource q π U t, ?_⟩
  calc q (strictTransformToSource q π U t)
      = (strictTransformToSource q π U ≫ q) t := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (strictTransformMap q π U ≫ π) t := by rw [strictTransformToSource_comp]
    _ = π (strictTransformMap q π U t) := Scheme.Hom.comp_apply _ _ _

/-- The strict transform of `q` contains the whole locus over the preserved open: a
point of `X'` lying over `U` and over the image of `q` is in the range of the
strict-transform projection. -/
theorem mem_range_strictTransformMap {x' : X'} (hU : π x' ∈ U)
    (hq : π x' ∈ Set.range q) :
    x' ∈ Set.range (strictTransformMap q π U) := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z x' hz
  have hwU : w ∈ strictTransformOpen q π U := by
    change π (pullback.snd q π w) ∈ U
    rwa [hw2]
  obtain ⟨w₀, rfl⟩ : w ∈ Set.range (strictTransformOpen q π U).ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨strictTransformFactor q π U w₀, ?_⟩
  have h2 : strictTransformFactor q π U ≫ strictTransformMap q π U =
      (strictTransformOpen q π U).ι ≫ pullback.snd q π := by
    unfold strictTransformMap
    rw [strictTransformFactor_ι_assoc]
  calc strictTransformMap q π U (strictTransformFactor q π U w₀)
      = (strictTransformFactor q π U ≫ strictTransformMap q π U) w₀ :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = ((strictTransformOpen q π U).ι ≫ pullback.snd q π) w₀ := by rw [h2]
    _ = pullback.snd q π ((strictTransformOpen q π U).ι w₀) := Scheme.Hom.comp_apply _ _ _
    _ = x' := hw2

/-- The strict transform of a closed immersion along any modification is a closed
subscheme of the modified scheme. -/
theorem isClosedImmersion_strictTransformMap [IsClosedImmersion q] :
    IsClosedImmersion (strictTransformMap q π U) := by
  have : IsClosedImmersion (pullback.snd q π) := MorphismProperty.pullback_snd _ _ ‹_›
  unfold strictTransformMap
  infer_instance

/-- **Disjointness of boundary closures persists along strict transforms**
(blueprint: `lemma:nagata-boundary-disjoint-persists`; proof order item 37): if two
closed subschemes have disjoint images, their strict transforms along any
modification `π : X' ⟶ X` remain disjoint, because each strict transform is contained
in the full inverse image of the corresponding closed subscheme. -/
theorem StrictTransform.disjoint_of_disjoint {Z₁ Z₂ : Scheme.{u}}
    (q₁ : Z₁ ⟶ X) (q₂ : Z₂ ⟶ X) (hdisj : Disjoint (Set.range q₁) (Set.range q₂)) :
    Disjoint (Set.range (strictTransformMap q₁ π U))
      (Set.range (strictTransformMap q₂ π U)) :=
  ((hdisj.preimage π).mono
    (range_strictTransformMap_subset_preimage q₁ π U)
    (range_strictTransformMap_subset_preimage q₂ π U))

end StrictTransformRange

section BoundarySeparation

variable {X : Scheme.{u}} {U : X.Opens}

/-- The closure of the inverse image of the `U`-part of a closed center is contained
in the range of its strict transform along a `U`-admissible blow-up. -/
theorem IsAdmissible.closure_preimage_subset_range_strictTransformMap
    (B : IsAdmissible X U) (I : X.IdealSheafData) {T : Set U.toScheme}
    (hT : T ⊆ U.ι ⁻¹' (I.support : Set X)) :
    closure (B.I.blowupMap ⁻¹' (U.ι '' T)) ⊆
      Set.range (strictTransformMap I.subschemeι B.I.blowupMap B.preservedOpen) := by
  have : IsClosedImmersion
      (strictTransformMap I.subschemeι B.I.blowupMap B.preservedOpen) :=
    isClosedImmersion_strictTransformMap I.subschemeι B.I.blowupMap B.preservedOpen
  refine closure_minimal ?_
    (strictTransformMap I.subschemeι B.I.blowupMap
      B.preservedOpen).isClosedEmbedding.isClosed_range
  intro x' hx'
  obtain ⟨t, htT, heq⟩ := Set.mem_preimage.mp hx'
  have hmemU : B.I.blowupMap x' ∈ U := by
    rw [← heq]
    have : U.ι t ∈ Set.range U.ι := ⟨t, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  refine mem_range_strictTransformMap I.subschemeι B.I.blowupMap B.preservedOpen
    (B.le_preservedOpen hmemU) ?_
  rw [Scheme.IdealSheafData.range_subschemeι, ← heq]
  exact hT htT

/-- **The constructible-boundary separation blow-up** (Stacks Project Tags 080P and
0F3V): let `X` be qcqs, `U ⊆ X` a quasi-compact open, and let `T₁`, `T₂` be disjoint
closed subsets of `U` with quasi-compact complements (i.e. constructible closed
subsets of `U`). Then there is a `U`-admissible blow-up of `X` in which the closures
of the inverse images of `T₁` and `T₂` are disjoint.

The blow-up is the boundary-separation blow-up of the sum of two finite-type ideals
`I₁`, `I₂` extending the vanishing ideals of `T₁`, `T₂` from `U` (Stacks Tags 01PH
and 01PF); the closure of the inverse image of `Tᵢ` is contained in the strict
transform of `V(Iᵢ)` (`closure_preimage_subset_range_strictTransformMap`), and these
strict transforms are disjoint by `disjoint_range_strictTransformMap_sup`.
(Blueprint: `def:nagata-separate-constructible-closed`,
`lemma:nagata-separate-constructible-closed`,
`def:nagata-two-open-prepared-boundaries`, `lemma:nagata-prepared-boundaries`;
proof order item 36.) -/
theorem exists_admissibleBlowup_disjoint_closures
    [CompactSpace X] [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X))
    {T₁ T₂ : Set U.toScheme} (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂)
    (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ) (hdisj : Disjoint T₁ T₂) :
    ∃ B : IsAdmissible X U,
      Disjoint (closure (B.I.blowupMap ⁻¹' (U.ι '' T₁)))
        (closure (B.I.blowupMap ⁻¹' (U.ι '' T₂))) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  -- the finite-type vanishing ideals of `T₁`, `T₂` on `U`
  obtain ⟨J₁, hJ₁ft, hJ₁supp⟩ := U.toScheme.exists_finiteType_ideal_coe_support_eq_compl
    ⟨T₁ᶜ, hT₁.isOpen_compl⟩ hc₁
  obtain ⟨J₂, hJ₂ft, hJ₂supp⟩ := U.toScheme.exists_finiteType_ideal_coe_support_eq_compl
    ⟨T₂ᶜ, hT₂.isOpen_compl⟩ hc₂
  -- extend them to finite-type ideals on `X`
  obtain ⟨I₁, hI₁ft, hI₁comap⟩ :=
    Scheme.IdealSheafData.exists_finiteType_comap_eq U hU J₁ hJ₁ft
  obtain ⟨I₂, hI₂ft, hI₂comap⟩ :=
    Scheme.IdealSheafData.exists_finiteType_comap_eq U hU J₂ hJ₂ft
  -- the supports of the extensions restrict to `T₁`, `T₂` on `U`
  have hpre₁ : U.ι ⁻¹' (I₁.support : Set X) = T₁ := by
    have h1 : ((I₁.comap U.ι).support : Set U.toScheme) =
        U.ι ⁻¹' (I₁.support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    rw [← h1, hI₁comap, hJ₁supp]
    exact compl_compl T₁
  have hpre₂ : U.ι ⁻¹' (I₂.support : Set X) = T₂ := by
    have h1 : ((I₂.comap U.ι).support : Set U.toScheme) =
        U.ι ⁻¹' (I₂.support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    rw [← h1, hI₂comap, hJ₂supp]
    exact compl_compl T₂
  -- the common support misses `U`
  have hdisjX : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X)) := by
    rw [Set.disjoint_left]
    rintro x hxU ⟨hx1, hx2⟩
    obtain ⟨t, rfl⟩ : x ∈ Set.range U.ι := by
      rwa [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mp hdisj (hpre₁ ▸ Set.mem_preimage.mpr hx1)
      (hpre₂ ▸ Set.mem_preimage.mpr hx2)
  -- blow up the sum of the ideals
  refine ⟨separationBlowup I₁ I₂ hI₁ft hI₂ft hdisjX, ?_⟩
  refine Disjoint.mono
    ((separationBlowup I₁ I₂ hI₁ft hI₂ft
      hdisjX).closure_preimage_subset_range_strictTransformMap I₁ hpre₁.symm.le)
    ((separationBlowup I₁ I₂ hI₁ft hI₂ft
      hdisjX).closure_preimage_subset_range_strictTransformMap I₂ hpre₂.symm.le) ?_
  exact disjoint_range_strictTransformMap_sup I₁ I₂ hI₁ft hI₂ft

end BoundarySeparation

end AlgebraicGeometry
