/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Pushouts of schemes along open immersions

If `f : W ⟶ Y` and `g : W ⟶ Z` are open immersions of schemes, the pushout of `f` and `g`
exists: the span `Y ⟵ W ⟶ Z` is a locally directed diagram of open immersions, so the
gluing machinery of `Mathlib.AlgebraicGeometry.Gluing` applies. In this file we develop the
basic geometry of this pushout `P`:

- `AlgebraicGeometry.Scheme.isOpenImmersion_pushout_inl` (and `_inr`): the coprojections
  `Y ⟶ P` and `Z ⟶ P` are open immersions;
- `AlgebraicGeometry.Scheme.opensRange_pushout_inl_sup_opensRange_pushout_inr`: the images
  of `Y` and `Z` cover `P`;
- `AlgebraicGeometry.Scheme.isPullback_of_isOpenImmersion_pushout`: the pushout square is
  also a pullback square, i.e. `W` is the intersection of `Y` and `Z` inside `P`;
- `AlgebraicGeometry.Scheme.preimage_opensRange_pushout_inl_of_isPullback`: given a morphism
  of such spans whose `Z`-square is cartesian, the induced morphism on pushouts pulls the
  image of `Y` back to the image of `Y'`, and the `Y`-square of pushouts is cartesian
  (`AlgebraicGeometry.Scheme.isPullback_pushout_map_inl_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : W ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]

instance isOpenImmersion_span_map : ∀ {i j : WalkingSpan} (h : i ⟶ j),
    IsOpenImmersion ((span f g).map h)
  | _, _, .id X => inferInstanceAs (IsOpenImmersion (𝟙 ((span f g).obj X)))
  | _, _, .init .left => inferInstanceAs (IsOpenImmersion f)
  | _, _, .init .right => inferInstanceAs (IsOpenImmersion g)

instance hasPushout_of_isOpenImmersion : HasPushout f g :=
  inferInstanceAs (HasColimit (span f g))

instance isOpenImmersion_pushout_inl : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.left))

instance isOpenImmersion_pushout_inr : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.right))

lemma pushout_inl_eq_inr_iff (x : Y) (y : Z) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ w : W, f w = x ∧ g w = y := by
  rw [show pushout.inl f g x = pushout.inr f g y ↔
      colimit.ι (span f g) WalkingSpan.left x = colimit.ι (span f g) WalkingSpan.right y from
    Iff.rfl, IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨k, fi, fj, w, hx, hy⟩
    obtain (_ | ⟨_ | _⟩) := k
    · rw [Subsingleton.elim fi WalkingSpan.Hom.fst] at hx
      rw [Subsingleton.elim fj WalkingSpan.Hom.snd] at hy
      exact ⟨w, hx, hy⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, hx, hy⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, w, hx, hy⟩

lemma opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [TopologicalSpace.Opens.mem_sup]
  obtain ⟨k, y, rfl⟩ := IsLocallyDirected.ι_jointly_surjective (span f g) x
  obtain (_ | ⟨_ | _⟩) := k
  · refine Or.inl ⟨(span f g).map WalkingSpan.Hom.fst y, ?_⟩
    rw [show pushout.inl f g ((span f g).map WalkingSpan.Hom.fst y) =
      ((span f g).map WalkingSpan.Hom.fst ≫ colimit.ι (span f g) WalkingSpan.left) y from
      (Scheme.Hom.comp_apply ..), colimit.w]
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

lemma preimage_opensRange_pushout_inl :
    pushout.inr f g ⁻¹ᵁ (pushout.inl f g).opensRange = g.opensRange := by
  ext z
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨w, -, rfl⟩ := (pushout_inl_eq_inr_iff f g y z).mp hy
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨f w, (pushout_inl_eq_inr_iff f g _ _).mpr ⟨w, rfl, rfl⟩⟩

lemma preimage_opensRange_pushout_inr :
    pushout.inl f g ⁻¹ᵁ (pushout.inr f g).opensRange = f.opensRange := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl, -⟩ := (pushout_inl_eq_inr_iff f g y z).mp hz.symm
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨g w, ((pushout_inl_eq_inr_iff f g _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

/-- The pushout square of two open immersions is also a pullback square:
`W` is the intersection of (the images of) `Y` and `Z` inside the pushout. -/
lemma isPullback_of_isOpenImmersion_pushout :
    IsPullback f g (pushout.inl f g) (pushout.inr f g) :=
  IsOpenImmersion.isPullback f g (pushout.inl f g) (pushout.inr f g)
    pushout.condition.symm (preimage_opensRange_pushout_inl f g)

section Map

variable {W' Y' Z' : Scheme.{u}} (f' : W' ⟶ Y') (g' : W' ⟶ Z')
  [IsOpenImmersion f'] [IsOpenImmersion g']
  (u : Y' ⟶ Y) (β : Z' ⟶ Z) (γ : W' ⟶ W)
  (hf : γ ≫ f = f' ≫ u) (hg : γ ≫ g = g' ≫ β)

include hf hg in
lemma preimage_opensRange_pushout_inl_of_isPullback (H : IsPullback γ g' g β) :
    pushout.map f' g' f g u β γ hf.symm hg.symm ⁻¹ᵁ (pushout.inl f g).opensRange =
      (pushout.inl f' g').opensRange := by
  apply le_antisymm
  · rintro p hp
    have : p ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨z', rfl⟩) := this
    · exact hmem
    · replace hp : (pushout.inr f' g' ≫ pushout.map f' g' f g u β γ hf.symm hg.symm) z' ∈
          (pushout.inl f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inr_desc] at hp
      obtain ⟨y, hy⟩ := hp
      obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff f g y (β z')).mp
        (by rwa [Scheme.Hom.comp_apply] at hy)
      obtain ⟨w', -, rfl⟩ := exists_preimage_of_isPullback H w z' hw
      show pushout.inr f' g' (g' w') ∈ (pushout.inl f' g').opensRange
      exact ⟨f' w', (pushout_inl_eq_inr_iff f' g' _ _).mpr ⟨w', rfl, rfl⟩⟩
  · rintro p ⟨y', rfl⟩
    show (pushout.inl f' g' ≫ pushout.map f' g' f g u β γ hf.symm hg.symm) y' ∈
      (pushout.inl f g).opensRange
    rw [pushout.inl_desc, Scheme.Hom.comp_apply]
    exact ⟨u y', rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `Z`-component square is cartesian,
the `Y`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inl_of_isPullback (H : IsPullback γ g' g β) :
    IsPullback u (pushout.inl f' g') (pushout.inl f g)
      (pushout.map f' g' f g u β γ hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inl_desc _ _ _)
    (preimage_opensRange_pushout_inl_of_isPullback f g f' g' u β γ hf hg H)

include hf hg in
lemma preimage_opensRange_pushout_inr_of_isPullback (H : IsPullback γ f' f u) :
    pushout.map f' g' f g u β γ hf.symm hg.symm ⁻¹ᵁ (pushout.inr f g).opensRange =
      (pushout.inr f' g').opensRange := by
  apply le_antisymm
  · rintro p hp
    have : p ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨y', rfl⟩ | hmem) := this
    · replace hp : (pushout.inl f' g' ≫ pushout.map f' g' f g u β γ hf.symm hg.symm) y' ∈
          (pushout.inr f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inl_desc] at hp
      obtain ⟨z, hz⟩ := hp
      obtain ⟨w, hw, -⟩ := (pushout_inl_eq_inr_iff f g (u y') z).mp
        (by rw [Scheme.Hom.comp_apply] at hz; exact hz.symm)
      obtain ⟨w', -, rfl⟩ := exists_preimage_of_isPullback H w y' hw
      show pushout.inl f' g' (f' w') ∈ (pushout.inr f' g').opensRange
      exact ⟨g' w', ((pushout_inl_eq_inr_iff f' g' _ _).mpr ⟨w', rfl, rfl⟩).symm⟩
    · exact hmem
  · rintro p ⟨z', rfl⟩
    show (pushout.inr f' g' ≫ pushout.map f' g' f g u β γ hf.symm hg.symm) z' ∈
      (pushout.inr f g).opensRange
    rw [pushout.inr_desc, Scheme.Hom.comp_apply]
    exact ⟨β z', rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `Y`-component square is cartesian,
the `Z`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inr_of_isPullback (H : IsPullback γ f' f u) :
    IsPullback β (pushout.inr f' g') (pushout.inr f g)
      (pushout.map f' g' f g u β γ hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inr_desc _ _ _)
    (preimage_opensRange_pushout_inr_of_isPullback f g f' g' u β γ hf hg H)

end Map

end AlgebraicGeometry.Scheme
