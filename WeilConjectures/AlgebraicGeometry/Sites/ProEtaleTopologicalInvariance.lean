/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleTopologicalInvariance.Site
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Topological invariance of the small pro-étale site

Let `r : X ⟶ Y` be a universal homeomorphism of schemes. We show that base change
`V ↦ V ×_Y X` exhibits the small pro-étale site of `Y` as a dense subsite of the small
pro-étale site of `X` (`Functor.IsDenseSubsite`). By the comparison lemma, restriction along
base change is then an equivalence between the categories of sheaves on the two sites. This is
the pro-étale counterpart of `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`,
and it follows [Bhatt–Scholze, Lemma 5.4.2]; see also blueprint `sk-i-topology`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.ext_of_surjective_of_weaklyEtale`: two `Y`-morphisms into a
  weakly étale `Y`-scheme that agree after precomposition with a surjection are equal.
- `AlgebraicGeometry.Scheme.ProEt.faithful_overPullback`: base change along a surjective
  morphism is faithful on small pro-étale sites.
- `AlgebraicGeometry.Scheme.ProEt.functorPushforward_overPullback_mem_iff`: base change along a
  universal homeomorphism preserves and reflects pro-étale coverings.
- `AlgebraicGeometry.Scheme.ProEt.isLocallyFull_overPullback`: base change along a universal
  homeomorphism is locally full.
- `AlgebraicGeometry.Scheme.ProEt.isDenseSubsite_overPullback`: base change along a universal
  homeomorphism exhibits `Y.ProEt` as a dense subsite of `X.ProEt`.

## Proof sketch

Faithfulness: the locus where two morphisms into a weakly étale `Y`-scheme agree is the
pullback of the diagonal, a flat immersion; if it is surjective it is a flat, surjective,
quasi-compact monomorphism, hence an isomorphism by fpqc descent.

Cover-density is `AlgebraicGeometry.Scheme.ProEt.isCoverDense_overPullback`. Local fullness
follows from it: an `X`-morphism `f : V ×_Y X ⟶ W ×_Y X` is a section `s` of the base change of
`P = V ×_Y W ⟶ V`, and covering `V ×_Y X`, as a scheme over `P ×_Y X` via `s`, by base
changes of schemes weakly étale over `P` lifts `f` locally. Reflection of coverings holds since
`V ×_Y X ⟶ V` is a homeomorphism after every base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Two `Y`-morphisms `a b : T ⟶ V` into a weakly étale `Y`-scheme `V` are equal if they agree
after precomposition with a surjection `π : T' ⟶ T`. The locus where `a` and `b` agree is the
pullback of the diagonal of `V ⟶ Y`, a flat immersion; it is surjective, hence an isomorphism by
fpqc descent. -/
lemma Scheme.Hom.ext_of_surjective_of_weaklyEtale {T' T V Y : Scheme.{u}} (π : T' ⟶ T)
    [Surjective π] (v : V ⟶ Y) [WeaklyEtale v] {a b : T ⟶ V} (hab : a ≫ v = b ≫ v)
    (h : π ≫ a = π ≫ b) : a = b := by
  let e : T ⟶ pullback v v := pullback.lift a b hab
  have he : π ≫ e = (π ≫ a) ≫ pullback.diagonal v := by
    apply pullback.hom_ext <;> simp [e, h]
  -- the locus `E ⟶ T` where `a` and `b` agree
  let p : pullback e (pullback.diagonal v) ⟶ T := pullback.fst _ _
  have hsurj : Function.Surjective p := by
    intro t
    obtain ⟨t', rfl⟩ := π.surjective t
    have : e (π t') = pullback.diagonal v ((π ≫ a) t') := by
      rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (π t') ((π ≫ a) t') this
    exact ⟨z, hz⟩
  have : Surjective p := ⟨hsurj⟩
  have : QuasiCompact p := by
    refine ⟨fun U _ hU ↦ ?_⟩
    refine p.isEmbedding.isInducing.isCompact_preimage ?_ hU
    rw [hsurj.range_eq]
    exact isClosed_univ
  -- `p` is a flat, surjective, quasi-compact monomorphism, hence an isomorphism
  have : IsIso p := MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := p) (g := p)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (inferInstanceAs (IsIso (pullback.fst p p)))
  have hp : p ≫ e = pullback.snd _ _ ≫ pullback.diagonal v := pullback.condition
  have ha : a = inv p ≫ pullback.snd e (pullback.diagonal v) := by
    rw [IsIso.eq_inv_comp, show a = e ≫ pullback.fst v v by simp [e], reassoc_of% hp,
      pullback.diagonal_fst, Category.comp_id]
  have hb : b = inv p ≫ pullback.snd e (pullback.diagonal v) := by
    rw [IsIso.eq_inv_comp, show b = e ≫ pullback.snd v v by simp [e], reassoc_of% hp,
      pullback.diagonal_snd, Category.comp_id]
  rw [ha, hb]

namespace Scheme.ProEt

variable {X Y : Scheme.{u}} (r : X ⟶ Y)

/-- Base change along a surjective morphism is faithful on small pro-étale sites. -/
instance faithful_overPullback [Surjective r] :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).Faithful where
  map_injective {V W} g h e := by
    apply MorphismProperty.Over.Hom.ext
    refine Scheme.Hom.ext_of_surjective_of_weaklyEtale (pullback.fst V.hom r) W.hom
      (by rw [MorphismProperty.Over.w g, MorphismProperty.Over.w h]) ?_
    have := congr(($e).left ≫ pullback.fst W.hom r)
    simpa using this

/-- Base change along a surjective morphism is locally faithful on small pro-étale sites. -/
instance isLocallyFaithful_overPullback [Surjective r] :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).IsLocallyFaithful (topology X) where
  functorPushforward_equalizer_mem {V W} f₁ f₂ e := by
    obtain rfl := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map_injective e
    rw [Sieve.equalizer_self, Sieve.functorPushforward_top]
    exact GrothendieckTopology.top_mem _ _

/-- A morphism of the small pro-étale site is weakly étale. -/
instance weaklyEtale_left {U V : X.ProEt} (f : U ⟶ V) : WeaklyEtale f.left := by
  have : WeaklyEtale (f.left ≫ V.hom) := by rw [MorphismProperty.Over.w f]; infer_instance
  exact WeaklyEtale.of_comp f.left V.hom

variable [IsUniversalHomeomorphism r]

/-- Base change along a universal homeomorphism reflects pro-étale coverings: the
quasi-compactness and joint surjectivity of a family of morphisms into `V` can be checked after
base change along the universal homeomorphism `V ×_Y X ⟶ V`. -/
lemma mem_topology_of_functorPushforward_overPullback_mem {V : Y.ProEt} {S : Sieve V}
    (hS : S.functorPushforward (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r) ∈
      topology X ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj V)) :
    S ∈ topology Y V := by
  set u := MorphismProperty.Over.pullback @WeaklyEtale ⊤ r
  obtain ⟨R, hR, hle⟩ := mem_topology_iff.mp hS
  obtain ⟨ι, Z, h, rfl⟩ := R.exists_eq_ofArrows
  have hh : ∀ i, ∃ (W : Y.ProEt) (s : W ⟶ V) (z : Z i ⟶ u.obj W), S s ∧ h i = z ≫ u.map s :=
    fun i ↦ hle (Z i) (h i) (Presieve.ofArrows.mk i)
  choose W s z hs hzs using hh
  rw [mem_topology_iff]
  refine ⟨Presieve.ofArrows W s, ?_, fun _ _ ⟨i⟩ ↦ hs i⟩
  rw [mem_precoverage_iff, Presieve.map_ofArrows] at hR ⊢
  obtain ⟨hRqc, hRp⟩ := hR
  rw [ofArrows_mem_precoverage_iff] at hRp
  -- the projection `π : V ×_Y X ⟶ V` and the factorisations through the `s i`
  let π := pullback.fst V.hom r
  let t : ∀ i, (Z i).left ⟶ (W i).left := fun i ↦ (z i).left ≫ pullback.fst (W i).hom r
  have hfac : ∀ i, (h i).left ≫ π = t i ≫ (s i).left := by
    intro i
    have : (u.map (s i)).left ≫ π = pullback.fst (W i).hom r ≫ (s i).left :=
      pullback.lift_fst _ _ _
    rw [hzs i]
    change ((z i).left ≫ (u.map (s i)).left) ≫ π = _
    rw [Category.assoc, this, ← Category.assoc]
  refine ⟨?_, ?_⟩
  · -- quasi-compactness
    have hR' : QuasiCompactCover (⟨ι, fun i ↦ (Z i).left, fun i ↦ (h i).left⟩ :
        PreZeroHypercover (u.obj V).left) := presieve₀_mem_qcPrecoverage_iff.mp hRqc
    refine presieve₀_mem_qcPrecoverage_iff
      (E := ⟨ι, fun i ↦ (W i).left, fun i ↦ (s i).left⟩) |>.mpr ⟨fun {K} hK ↦ ?_⟩
    have hK' : IsAffineOpen (π ⁻¹ᵁ K) := hK.preimage π
    obtain ⟨t₀, ht₀, O, hOc, hOU⟩ := hR'.isCompactOpenCovered_of_isAffineOpen hK'
    have hg : IsCompactOpenCovered (fun i ↦ ((h i).left ≫ π).base) (K : Set V.left) := by
      refine ⟨t₀, ht₀, O, hOc, ?_⟩
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, y, hy, rfl⟩
        have h1 : (h i).left y ∈ ⋃ j, ⋃ (hj : j ∈ t₀), (h j).left '' (O j hj : Set _) :=
          Set.mem_iUnion₂.mpr ⟨i, hi, y, hy, rfl⟩
        rw [hOU] at h1
        exact h1
      · intro hx
        obtain ⟨x', rfl⟩ := π.surjective x
        have h2 : x' ∈ ⋃ j, ⋃ (hj : j ∈ t₀), (h j).left '' (O j hj : Set _) := by
          rw [hOU]
          exact hx
        obtain ⟨i, hi, y, hy, rfl⟩ := Set.mem_iUnion₂.mp h2
        exact ⟨i, hi, y, hy, rfl⟩
    exact hg.of_comp (fun i ↦ ((h i).left ≫ π).base) (a := id) (fun i ↦ (t i).base)
      (fun i ↦ (t i).continuous) (fun i ↦ by rw [hfac]; rfl) (fun i ↦ (s i).left.continuous)
      K.isOpen
  · -- joint surjectivity
    refine (ofArrows_mem_precoverage_iff _).mpr ⟨fun v ↦ ?_, fun i ↦ weaklyEtale_left (s i)⟩
    obtain ⟨x, rfl⟩ := π.surjective v
    obtain ⟨i, y, rfl⟩ := hRp.1 x
    refine ⟨i, t i y, ?_⟩
    change (s i).left (t i y) = π ((h i).left y)
    rw [← Scheme.Hom.comp_apply, ← hfac i]
    rfl

/-- Base change along a universal homeomorphism preserves and reflects pro-étale coverings. -/
lemma functorPushforward_overPullback_mem_iff {V : Y.ProEt} {S : Sieve V} :
    S.functorPushforward (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r) ∈
      topology X ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj V) ↔
    S ∈ topology Y V :=
  ⟨mem_topology_of_functorPushforward_overPullback_mem r,
    (coverPreserving_overPullback r).cover_preserve⟩

end Scheme.ProEt

end AlgebraicGeometry
