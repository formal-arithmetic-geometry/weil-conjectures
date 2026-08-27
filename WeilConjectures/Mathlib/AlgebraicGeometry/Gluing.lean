/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Pushouts of open immersions of schemes

Two open immersions `f : U ⟶ X`, `g : U ⟶ Y` with common source form a span whose maps
are all open immersions, so Mathlib's locally directed gluing provides its colimit: the
pushout `X ⊔_U Y`, i.e. the scheme obtained by gluing `X` and `Y` along `U`. This file
records the basic geometry of this pushout:

- `AlgebraicGeometry.IsOpenImmersion.hasPushout`: the pushout exists;
- the inclusions `pushout.inl`/`pushout.inr` are open immersions and are jointly
  surjective (`AlgebraicGeometry.range_pushout_inl_union_range_pushout_inr`);
- `AlgebraicGeometry.IsOpenImmersion.isPullback_pushout`: the pushout square is also a
  pullback square, i.e. the two charts intersect in exactly the glued copy of `U`;
- `CompactSpace` transfers from the two charts to the pushout;
- `AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc`: a source-local property holds
  for `pushout.desc h k w` as soon as it holds for `h` and `k`;
- `AlgebraicGeometry.QuasiCompact.pushout_desc` and
  `AlgebraicGeometry.IsSeparated.pushout_desc`: quasi-compactness and (given that the
  graph `U ⟶ X ×_S Y` is a closed immersion) separatedness of the glued morphism.

These are the raw ingredients for the intermediate schemes `Wᵢ = U ⊔_{Uᵢ} Xᵢ°` of the
two-open compactification theorem (blueprint chapter "Nagata compactification",
`def:nagata-two-open-intermediate-schemes`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- Every arrow of the span of two open immersions is an open immersion: the two
non-identity arrows are `f` and `g` themselves. This is what makes the span a locally
directed diagram, hence gluable. -/
instance IsOpenImmersion.span_map : ∀ {i j : WalkingSpan} (h : i ⟶ j),
    IsOpenImmersion ((span f g).map h)
  | _, _, .id _ => by rw [span_map_id]; infer_instance
  | _, _, .init WalkingPair.left => inferInstanceAs (IsOpenImmersion f)
  | _, _, .init WalkingPair.right => inferInstanceAs (IsOpenImmersion g)

/-- The pushout of two open immersions of schemes with common source exists: the span
is a locally directed diagram of open immersions, glued by
`AlgebraicGeometry.Scheme.IsLocallyDirected`. -/
instance IsOpenImmersion.hasPushout : HasPushout f g :=
  inferInstanceAs (HasColimit (span f g))

instance : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.left))

instance : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.right))

/-- The two charts of the pushout of two open immersions cover the pushout. -/
lemma range_pushout_inl_union_range_pushout_inr :
    Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  match i, y with
  | .left, y => exact Or.inl ⟨y, rfl⟩
  | .right, y => exact Or.inr ⟨y, rfl⟩
  | .zero, y =>
    refine Or.inl ⟨f y, ?_⟩
    calc pushout.inl f g (f y)
        = ((span f g).map WalkingSpan.Hom.fst ≫ colimit.ι (span f g) WalkingSpan.left) y :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = colimit.ι (span f g) WalkingSpan.zero y := by
          rw [colimit.w (span f g) WalkingSpan.Hom.fst]

/-- **The pushout square of two open immersions of schemes is also a pullback square**:
the two charts of the glued scheme intersect in exactly the glued copy of the common
source. -/
theorem IsOpenImmersion.isPullback_pushout :
    IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  have hrange : ∀ (T : Scheme.{u}) (s₁ : T ⟶ X) (s₂ : T ⟶ Y),
      s₁ ≫ pushout.inl f g = s₂ ≫ pushout.inr f g →
      ∀ t : T, ∃ u : U, f u = s₁ t ∧ g u = s₂ t := by
    intro T s₁ s₂ hs t
    have ht : colimit.ι (span f g) WalkingSpan.left (s₁ t) =
        colimit.ι (span f g) WalkingSpan.right (s₂ t) := by
      calc colimit.ι (span f g) WalkingSpan.left (s₁ t)
          = (s₁ ≫ pushout.inl f g) t := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (s₂ ≫ pushout.inr f g) t := by rw [hs]
        _ = colimit.ι (span f g) WalkingSpan.right (s₂ t) := Scheme.Hom.comp_apply _ _ _
    obtain ⟨k, fi, fj, u, hu₁, hu₂⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp ht
    cases fi with
    | id => exact nomatch fj
    | init j => cases fj with
      | init j' => exact ⟨u, hu₁, hu₂⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk pushout.condition
    (fun s ↦ IsOpenImmersion.lift f s.fst ?_) (fun s ↦ IsOpenImmersion.lift_fac _ _ _)
    (fun s ↦ ?_) (fun s m hm₁ _ ↦ ?_))
  · rintro - ⟨t, rfl⟩
    obtain ⟨u, hu, -⟩ := hrange s.pt s.fst s.snd s.condition t
    exact ⟨u, hu⟩
  · rw [← cancel_mono (pushout.inr f g), Category.assoc, ← pushout.condition,
      IsOpenImmersion.lift_fac_assoc]
    exact s.condition
  · rw [← cancel_mono f, hm₁, IsOpenImmersion.lift_fac]

instance [CompactSpace X] [CompactSpace Y] : CompactSpace ↑(pushout f g) := by
  constructor
  rw [← range_pushout_inl_union_range_pushout_inr f g]
  exact (isCompact_range (pushout.inl f g).continuous).union
    (isCompact_range (pushout.inr f g).continuous)

/-- The two charts `X` and `Y` as an open cover of the pushout `X ⊔_U Y`. -/
@[simps! I₀ X f]
def IsOpenImmersion.pushoutCover : (pushout f g).OpenCover :=
  Scheme.Cover.mkOfCovers WalkingPair (fun j ↦ WalkingPair.casesOn j X Y)
    (fun j ↦ WalkingPair.casesOn j (pushout.inl f g) (pushout.inr f g))
    (fun x ↦ by
      have hx : x ∈ Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) := by
        rw [range_pushout_inl_union_range_pushout_inr f g]
        trivial
      obtain ⟨y, hy⟩ | ⟨y, hy⟩ := hx
      exacts [⟨WalkingPair.left, y, hy⟩, ⟨WalkingPair.right, y, hy⟩])
    (fun j ↦ by cases j <;> infer_instance)

/-- **Source-local properties descend to a pushout of open immersions**: if `P` is
Zariski-local on the source and holds for `h : X ⟶ S` and `k : Y ⟶ S`, then it holds
for the glued morphism `pushout.desc h k w : X ⊔_U Y ⟶ S`. -/
lemma IsZariskiLocalAtSource.pushout_desc {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) (hh : P h) (hk : P k) : P (pushout.desc h k w) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (IsOpenImmersion.pushoutCover f g)]
  intro i
  cases i with
  | left => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inl_desc] using hh
  | right => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inr_desc] using hk

/-- **Quasi-compactness of a gluing of two schemes along a common open**: the inverse
image of a quasi-compact open under the glued morphism is the union of the images of the
two inverse images under `h` and `k`, hence quasi-compact. (Quasi-compactness of morphisms
is not Zariski-local on the source, so this does not follow from
`AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc`; what makes it work is that the
cover of the pushout has only two members.) -/
theorem QuasiCompact.pushout_desc {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) [QuasiCompact h] [QuasiCompact k] :
    QuasiCompact (pushout.desc h k w) := by
  constructor
  intro V hVopen hVcompact
  have hl : IsCompact (⇑h ⁻¹' V) := QuasiCompact.isCompact_preimage _ hVopen hVcompact
  have hr : IsCompact (⇑k ⁻¹' V) := QuasiCompact.isCompact_preimage _ hVopen hVcompact
  have hcov : ⇑(pushout.desc h k w) ⁻¹' V =
      ⇑(pushout.inl f g) '' (⇑h ⁻¹' V) ∪ ⇑(pushout.inr f g) '' (⇑k ⁻¹' V) := by
    apply subset_antisymm
    · intro p hp
      have hmem : p ∈ Set.range ⇑(pushout.inl f g) ∪ Set.range ⇑(pushout.inr f g) := by
        rw [range_pushout_inl_union_range_pushout_inr f g]
        trivial
      rcases hmem with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · refine Or.inl ⟨t, ?_, rfl⟩
        rwa [Set.mem_preimage, ← pushout.inl_desc (f := f) (g := g) h k w,
          Scheme.Hom.comp_apply]
      · refine Or.inr ⟨t, ?_, rfl⟩
        rwa [Set.mem_preimage, ← pushout.inr_desc (f := f) (g := g) h k w,
          Scheme.Hom.comp_apply]
    · rintro - (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, pushout.inl_desc]
        exact ht
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, pushout.inr_desc]
        exact ht
  rw [hcov]
  exact (hl.image (pushout.inl f g).continuous).union (hr.image (pushout.inr f g).continuous)

/-- **Separatedness of a gluing of two schemes along a common open**: let `h : X ⟶ S`
and `k : Y ⟶ S` be separated morphisms restricting to the same morphism on a common
open subscheme `U`, and assume the graph morphism `(f, g) : U ⟶ X ×_S Y` is a closed
immersion. Then the glued morphism `X ⊔_U Y ⟶ S` is separated. This is the form of the
two-open criterion (Stacks Project Tag 0F3U, `IsSeparated.of_two_open_cover`) used for
the intermediate schemes of the two-open compactification theorem. -/
theorem IsSeparated.pushout_desc {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) [IsSeparated h] [IsSeparated k]
    (hd : IsClosedImmersion (pullback.lift f g w)) :
    IsSeparated (pushout.desc h k w) := by
  have h₁ : IsSeparated (pushout.inl f g ≫ pushout.desc h k w) := by
    rw [pushout.inl_desc]
    infer_instance
  have h₂ : IsSeparated (pushout.inr f g ≫ pushout.desc h k w) := by
    rw [pushout.inr_desc]
    infer_instance
  refine IsSeparated.of_two_open_cover (pushout.desc h k w) (pushout.inl f g)
    (pushout.inr f g) (range_pushout_inl_union_range_pushout_inr f g) ?_
  have hp := IsOpenImmersion.isPullback_pushout f g
  have heq : pullback.map (pushout.inl f g) (pushout.inr f g)
      (pushout.inl f g ≫ pushout.desc h k w) (pushout.inr f g ≫ pushout.desc h k w)
      (𝟙 X) (𝟙 Y) (pushout.desc h k w) (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift f g w ≫
        (pullback.congrHom (pushout.inl_desc h k w) (pushout.inr_desc h k w)).inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_fst,
        Category.comp_id, hp.isoPullback_inv_fst]
    · simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_snd,
        Category.comp_id, hp.isoPullback_inv_snd]
  rw [heq]
  have := hd
  infer_instance

end AlgebraicGeometry
