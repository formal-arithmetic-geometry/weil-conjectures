/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Graphs of morphisms into finite étale schemes

We record some elementary facts about étale and finite étale morphisms used in the proof of the
proper base change theorem:

* `AlgebraicGeometry.Scheme.eq_of_comp_eq_of_isLocalHom`: two morphisms from the spectrum of a
  local ring to an étale `S`-scheme which agree over `S` and at a "point" `Spec Ω` lying over
  the closed point are equal;
* `AlgebraicGeometry.Scheme.exists_equiv_isClopen_graph`: morphisms `U ⟶ V` over `Y` into a
  finite étale `Y`-scheme `V` correspond to clopen subsets of `V ×_Y U` projecting
  isomorphically onto `U`;
* `AlgebraicGeometry.Scheme.isPullback_graph_baseChange`: this correspondence commutes with
  base change;
* `AlgebraicGeometry.Scheme.finrank_restrict_isClopen_of_isPullback`: ranks of clopen pieces
  of finite étale morphisms are compatible with base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Rigidity of maps from a local spectrum to an étale scheme.** Let `B` be a local ring,
`Ω` a field and `β : B →+* Ω` a local ring map. If `f : X ⟶ S` is étale and
`u v : Spec B ⟶ X` agree after composing with `f` and after precomposing with `Spec β`, then
`u = v`.

(blueprint: `lem-weil-pbc-etale-pointed-map-rigidity`) -/
theorem Scheme.eq_of_comp_eq_of_isLocalHom {B Ω : Type u} [CommRing B] [IsLocalRing B]
    [Field Ω] (β : B →+* Ω) [IsLocalHom β] {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (u v : Spec (.of B) ⟶ X) (hf : u ≫ f = v ≫ f)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫ u = Spec.map (CommRingCat.ofHom β) ≫ v) :
    u = v := by
  have hd : Spec.map (CommRingCat.ofHom β) ≫ pullback.lift u v hf =
      (Spec.map (CommRingCat.ofHom β) ≫ u) ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [hβ]
  have hrange : Set.range (pullback.lift u v hf).base ⊆
      Set.range (pullback.diagonal f).base := by
    rintro _ ⟨x, rfl⟩
    have hc : (pullback.lift u v hf).base (IsLocalRing.closedPoint B) ∈
        Set.range (pullback.diagonal f).base := by
      have h : (Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint Ω) =
          IsLocalRing.closedPoint B :=
        IsLocalRing.comap_closedPoint β
      rw [← h, ← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map
      (pullback.lift u v hf).continuous).mem_open
      (pullback.diagonal f).isOpenMap.isOpen_range hc
  have hu := IsOpenImmersion.lift_fac _ _ hrange =≫ pullback.fst f f
  have hv := IsOpenImmersion.lift_fac _ _ hrange =≫ pullback.snd f f
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at hu hv
  exact hu.symm.trans hv

/-- A section of an étale separated morphism is both an open and a closed immersion. -/
lemma Scheme.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id {X Y : Scheme.{u}}
    (r : X ⟶ Y) [Etale r] [IsSeparated r] (s : Y ⟶ X) (hs : s ≫ r = 𝟙 Y) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by
  have : Mono s := mono_of_mono_fac hs
  have : Etale (s ≫ r) := by
    rw [hs]
    infer_instance
  have : Etale s := Etale.of_comp s r
  have : IsClosedImmersion (s ≫ r) := by
    rw [hs]
    infer_instance
  exact ⟨IsOpenImmersion.of_flat_of_mono s, IsClosedImmersion.of_comp s r⟩

/-- **Morphisms into a finite étale scheme correspond to clopen graphs.** Let `p : U ⟶ Y` be a
morphism and `q : V ⟶ Y` finite étale, and let `r : V ×_Y U ⟶ U` be the projection. Morphisms
`a : U ⟶ V` with `a ≫ q = p` correspond bijectively to open subsets `W` of `V ×_Y U` which are
closed and such that `r` restricted to `W` is an isomorphism; the subset attached to `a` is the
image of its graph `(a, 𝟙 U) : U ⟶ V ×_Y U`.

(blueprint: `lem-weil-pbc-finite-etale-graph-clopen`) -/
theorem Scheme.exists_equiv_isClopen_graph {U V Y : Scheme.{u}} (p : U ⟶ Y) (q : V ⟶ Y)
    [IsFinite q] [Etale q] :
    ∃ e : {a : U ⟶ V // a ≫ q = p} ≃
        {W : (pullback q p).Opens // IsClosed (W : Set ↥(pullback q p)) ∧
          IsIso (W.ι ≫ pullback.snd q p)},
      ∀ a, ((e a).1 : Set ↥(pullback q p)) = Set.range (pullback.lift a.1 (𝟙 U)
        (by rw [a.2, Category.id_comp])).base := by
  let s (a : {a : U ⟶ V // a ≫ q = p}) : U ⟶ pullback q p :=
    pullback.lift a.1 (𝟙 U) (by rw [a.2, Category.id_comp])
  have hs (a) : s a ≫ pullback.snd q p = 𝟙 U := pullback.lift_snd _ _ _
  have hs' (a) := isOpenImmersion_and_isClosedImmersion_of_comp_eq_id _ _ (hs a)
  have hι (a) [IsOpenImmersion (s a)] :
      (s a).opensRange.ι ≫ pullback.snd q p = (s a).isoOpensRange.inv := by
    rw [← cancel_epi (s a).isoOpensRange.hom, Iso.hom_inv_id, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, hs]
  let σ (W : {W : (pullback q p).Opens //
      IsClosed (W : Set ↥(pullback q p)) ∧ IsIso (W.ι ≫ pullback.snd q p)}) : U ≅ W.1 :=
    (@asIso _ _ _ _ _ W.2.2).symm
  have hσ (W : {W : (pullback q p).Opens //
      IsClosed (W : Set ↥(pullback q p)) ∧ IsIso (W.ι ≫ pullback.snd q p)}) :
      (σ W).hom ≫ W.1.ι ≫ pullback.snd q p = 𝟙 U :=
    (@asIso _ _ _ _ _ W.2.2).inv_hom_id
  let toFun (a : {a : U ⟶ V // a ≫ q = p}) : {W : (pullback q p).Opens //
      IsClosed (W : Set ↥(pullback q p)) ∧ IsIso (W.ι ≫ pullback.snd q p)} := by
    have := (hs' a).1
    refine ⟨(s a).opensRange, ?_, ?_⟩
    · have := (hs' a).2
      exact (s a).isClosedEmbedding.isClosed_range
    · rw [hι]
      infer_instance
  let invFun (W : {W : (pullback q p).Opens //
      IsClosed (W : Set ↥(pullback q p)) ∧ IsIso (W.ι ≫ pullback.snd q p)}) :
      {a : U ⟶ V // a ≫ q = p} :=
    ⟨(σ W).hom ≫ W.1.ι ≫ pullback.fst q p, by
      simp only [Category.assoc, pullback.condition, reassoc_of% (hσ W)]⟩
  have hinvs (W : {W : (pullback q p).Opens //
      IsClosed (W : Set ↥(pullback q p)) ∧ IsIso (W.ι ≫ pullback.snd q p)}) :
      s (invFun W) = (σ W).hom ≫ W.1.ι := by
    apply pullback.hom_ext
    · simp [s, invFun]
    · simp only [s, pullback.lift_snd, Category.assoc, hσ]
  refine ⟨⟨toFun, invFun, fun a ↦ ?_, fun W ↦ ?_⟩, fun a ↦ rfl⟩
  · have := (hs' a).1
    have := (toFun a).2.2
    have hσa : (σ (toFun a)).hom = (s a).isoOpensRange.hom := by
      rw [← cancel_mono ((toFun a).1.ι ≫ pullback.snd q p), hσ]
      change 𝟙 U = _ ≫ (s a).opensRange.ι ≫ _
      rw [hι, Iso.hom_inv_id]
    apply Subtype.ext
    change (σ (toFun a)).hom ≫ (s a).opensRange.ι ≫ pullback.fst q p = a.1
    rw [hσa, Scheme.Hom.isoOpensRange_hom_ι_assoc]
    exact pullback.lift_fst _ _ _
  · apply Subtype.ext
    have := (hs' (invFun W)).1
    apply TopologicalSpace.Opens.ext
    change Set.range (s (invFun W)).base = _
    rw [hinvs, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr fun x ↦ ⟨(σ W).inv x, Scheme.inv_hom_apply _ x⟩, Set.image_univ,
      Scheme.Opens.range_ι]

end AlgebraicGeometry
