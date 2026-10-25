/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!

# Compactifications which are isomorphisms over an open

Let `F : A ⟶ Z` be a separated, quasi-compact morphism locally of finite type to a
quasi-compact quasi-separated scheme, and let `ι : V ⟶ Z` be a quasi-compact open immersion
over which `F` is an open immersion: `F ⁻¹ V ⟶ V` is an open immersion. Then `F` factors as an
open immersion `A ⟶ B` followed by a proper morphism `p : B ⟶ Z` which is an isomorphism over
`V` (`AlgebraicGeometry.exists_isProper_isPullback_of_isOpenImmersion`).

The construction glues `A` and `V` along `F ⁻¹ V` (a pushout of open immersions), which is
separated over `Z` since the graph of `F ⁻¹ V ⟶ V` is an isomorphism, takes a dense
compactification `B` of the glued scheme over `Z` (Nagata), and observes that the section
`V ⟶ p ⁻¹ V` is an open and closed immersion with dense image, hence an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {A A' V Z : Scheme.{u}} {F : A ⟶ Z} {ι : V ⟶ Z} {a : A' ⟶ A} {F' : A' ⟶ V}

/-- **Compactification which is an isomorphism over an open.** Let `F : A ⟶ Z` be separated,
quasi-compact and locally of finite type, `Z` quasi-compact and quasi-separated, and let
`ι : V ⟶ Z` be a quasi-compact open immersion such that the base change `F' : A' ⟶ V` of `F`
along `ι` is an open immersion. Then there are an open immersion `c : A ⟶ B` and a proper
morphism `p : B ⟶ Z` with `c ≫ p = F`, and a section `s : V ⟶ B` extending `c` on `A'`, which
identifies `V` with the inverse image `p ⁻¹ V`. -/
theorem exists_isProper_isPullback_of_isOpenImmersion [CompactSpace Z] [QuasiSeparatedSpace Z]
    [IsSeparated F] [QuasiCompact F] [LocallyOfFiniteType F] [IsOpenImmersion ι] [QuasiCompact ι]
    [IsOpenImmersion a] [IsOpenImmersion F'] (H : IsPullback a F' F ι) :
    ∃ (B : Scheme.{u}) (c : A ⟶ B) (p : B ⟶ Z) (s : V ⟶ B), IsOpenImmersion c ∧ IsProper p ∧
      c ≫ p = F ∧ a ≫ c = F' ≫ s ∧ IsPullback s (𝟙 V) p ι := by
  have w : a ≫ F = F' ≫ ι := H.w
  have hgraph : IsClosedImmersion (pullback.lift a F' w) := by
    have : pullback.lift a F' w = H.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    rw [this]
    infer_instance
  have : IsSeparated (pushout.desc F ι w) := IsSeparated.pushout_desc a F' w hgraph
  have : QuasiCompact (pushout.desc F ι w) := QuasiCompact.pushout_desc a F' w
  have : LocallyOfFiniteType (pushout.desc F ι w) :=
    IsZariskiLocalAtSource.pushout_desc a F' w ‹_› inferInstance
  let c₁ := denseCompactification (pushout.desc F ι w)
  have : IsSchemeTheoreticallyDominant c₁.i := denseCompactification_isDense _
  have : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion_iff.mpr inferInstance
  refine ⟨c₁.Z, pushout.inl a F' ≫ c₁.i, c₁.g, pushout.inr a F' ≫ c₁.i, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← c₁.comm, pushout.inl_desc]
  · rw [pushout.condition_assoc]
  have hs : (pushout.inr a F' ≫ c₁.i) ≫ c₁.g = 𝟙 V ≫ ι := by
    rw [Category.assoc, ← c₁.comm, pushout.inr_desc, Category.id_comp]
  let l : V ⟶ pullback c₁.g ι := pullback.lift _ _ hs
  have : IsClosedImmersion (l ≫ pullback.snd c₁.g ι) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.snd c₁.g ι)
  have : IsOpenImmersion (l ≫ pullback.fst c₁.g ι) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst c₁.g ι)
  have hsurj : Function.Surjective l := by
    by_contra hns
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Set.range l := by simpa [Function.Surjective] using hns
    have hO : IsOpen ((pullback.fst c₁.g ι) '' (Set.range l)ᶜ) :=
      (pullback.fst c₁.g ι).isOpenEmbedding.isOpenMap _
        l.isClosedEmbedding.isClosed_range.isOpen_compl
    obtain ⟨y, x', hx', hxy⟩ := c₁.i.denseRange.exists_mem_open hO ⟨_, x, hx, rfl⟩
    have key : ∃ v, pushout.inr a F' v = y := by
      have hy : y ∈ Set.range (pushout.inl a F') ∪ Set.range (pushout.inr a F') := by
        rw [range_pushout_inl_union_range_pushout_inr]
        trivial
      obtain ⟨b, rfl⟩ | h := hy
      · have hb : F b = ι (pullback.snd c₁.g ι x') := by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hxy,
            ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← c₁.comm, pushout.inl_desc]
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hb
        refine ⟨F' (H.isoPullback.inv z), ?_⟩
        rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply,
          ← Scheme.Hom.comp_apply H.isoPullback.inv a, H.isoPullback_inv_fst, hz]
      · exact h
    obtain ⟨v, rfl⟩ := key
    refine hx' ⟨v, (pullback.fst c₁.g ι).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, hxy, Scheme.Hom.comp_apply]
  have : IsIso l := (isIso_iff_isOpenImmersion_and_surjective l).2 ⟨inferInstance, ⟨hsurj⟩⟩
  exact IsPullback.of_iso_pullback ⟨hs⟩ (asIso l) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

end AlgebraicGeometry
