/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Pushouts of open immersions of schemes

Two open immersions `f : U ⟶ X`, `g : U ⟶ Y` with common source form a span whose maps
are all open immersions, so Mathlib's locally directed gluing provides its colimit: the
pushout `X ⊔_U Y`, i.e. the scheme obtained by gluing `X` and `Y` along `U`. This file
records the basic geometry of this pushout:

## Main results

- the inclusions `pushout.inl`/`pushout.inr` are open immersions and are jointly
  surjective (`AlgebraicGeometry.range_pushout_inl_union_range_pushout_inr`);
- `CompactSpace` transfers from the two charts to the pushout;
- `AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc`: a source-local property holds
  for `pushout.desc h k w` as soon as it holds for `h` and `k`;
- `AlgebraicGeometry.isPullback_pushout_map_inl_of_isPullback` and
  `AlgebraicGeometry.isPullback_pushout_map_inr_of_isPullback`: for a morphism of spans of
  open immersions with one cartesian component square, the corresponding component square
  of the induced morphism of pushouts is cartesian.

These are the raw ingredients for gluing a scheme out of two charts along their overlap, as
in the induction step of absolute Noetherian approximation.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

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
      obtain ⟨y, hy⟩ | ⟨y, hy⟩ :
          x ∈ Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) :=
        (range_pushout_inl_union_range_pushout_inr f g).ge (Set.mem_univ x)
      exacts [⟨WalkingPair.left, y, hy⟩, ⟨WalkingPair.right, y, hy⟩])
    (fun j ↦ by cases j <;> infer_instance)

/-- **Source-local properties descend to a pushout of open immersions**: if `P` is
Zariski-local on the source and holds for `h : X ⟶ S` and `k : Y ⟶ S`, then it holds
for the glued morphism `pushout.desc h k w : X ⊔_U Y ⟶ S`:

```
  X ─inl─▶ X ⊔_U Y ◀─inr─ Y
      ╲        │        ╱
       h    desc h k w  k
        ╲      ▼      ╱
          ──▶  S  ◀──
```
-/
lemma IsZariskiLocalAtSource.pushout_desc {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) (hh : P h) (hk : P k) : P (pushout.desc h k w) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (IsOpenImmersion.pushoutCover f g)]
  intro i
  cases i with
  | left => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inl_desc] using hh
  | right => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inr_desc] using hk

section PointsAndMap

/-!
### Points of the pushout, and morphisms of pushouts

The point-level description of the glued scheme: `inl x = inr y` if and only if `x` and
`y` have a common preimage in `U`. From this we deduce that the preimage of one chart
under the other chart's inclusion is exactly the image of `U`, and that for a morphism
of spans of open immersions with one cartesian component square, the corresponding
component square of the induced morphism of pushouts is cartesian as well.
-/

/-- **Points of the pushout of two open immersions**: a point of `X` and a point of `Y`
have the same image in `X ⊔_U Y` if and only if they have a common preimage in `U`. -/
lemma pushout_inl_eq_inr_iff (x : X) (y : Y) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ u : U, f u = x ∧ g u = y := by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).trans ?_
  constructor
  · rintro ⟨k, fi, fj, u, hx, hy⟩
    obtain (_ | ⟨_ | _⟩) := k
    · rw [Subsingleton.elim fi WalkingSpan.Hom.fst] at hx
      rw [Subsingleton.elim fj WalkingSpan.Hom.snd] at hy
      exact ⟨u, hx, hy⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨u, hx, hy⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, u, hx, hy⟩

/-- The two charts of the pushout of two open immersions cover it. -/
lemma opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [TopologicalSpace.Opens.mem_sup]
  exact Set.eq_univ_iff_forall.mp (range_pushout_inl_union_range_pushout_inr f g) x

/-- The preimage of the chart `Y` under the chart `X` of the pushout `X ⊔_U Y` is the
image of `U` in `X`. -/
lemma pushout_inl_preimage_opensRange_inr :
    pushout.inl f g ⁻¹ᵁ (pushout.inr f g).opensRange = f.opensRange := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl, -⟩ := (pushout_inl_eq_inr_iff f g y z).mp hz.symm
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨g u, ((pushout_inl_eq_inr_iff f g _ _).mpr ⟨u, rfl, rfl⟩).symm⟩

variable {U' X' Y' : Scheme.{u}} (f' : U' ⟶ X') (g' : U' ⟶ Y')
  [IsOpenImmersion f'] [IsOpenImmersion g']
  (α : X' ⟶ X) (β : Y' ⟶ Y) (γ : U' ⟶ U)
  (hf : γ ≫ f = f' ≫ α) (hg : γ ≫ g = g' ≫ β)

include hf hg in
/-- For a morphism of spans of open immersions whose `Y`-component square is cartesian, the
preimage of the chart `X` under the induced morphism of pushouts is the chart `X'`. -/
lemma pushout_map_preimage_opensRange_inl_of_isPullback (H : IsPullback γ g' g β) :
    pushout.map f' g' f g α β γ hf.symm hg.symm ⁻¹ᵁ (pushout.inl f g).opensRange =
      (pushout.inl f' g').opensRange := by
  apply le_antisymm
  · rintro p hp
    have : p ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]
      trivial
    obtain (hmem | ⟨z', rfl⟩) := this
    · exact hmem
    · replace hp : (pushout.inr f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) z' ∈
          (pushout.inl f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inr_desc] at hp
      obtain ⟨y, hy⟩ := hp
      obtain ⟨u, -, hu⟩ := (pushout_inl_eq_inr_iff f g y (β z')).mp
        (by rwa [Scheme.Hom.comp_apply] at hy)
      obtain ⟨u', -, rfl⟩ := Scheme.exists_preimage_of_isPullback H u z' hu
      exact ⟨f' u', (pushout_inl_eq_inr_iff f' g' _ _).mpr ⟨u', rfl, rfl⟩⟩
  · rintro p ⟨y', rfl⟩
    change (pushout.inl f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) y' ∈
      (pushout.inl f g).opensRange
    rw [pushout.inl_desc, Scheme.Hom.comp_apply]
    exact ⟨α y', rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `Y`-component square is cartesian,
the `X`-component square of the induced morphism of pushouts is cartesian:

```
  X' ◀──f'── U' ──g'──▶ Y'          X' ────▶ X' ⊔_{U'} Y'
  │          │          │           │             │
  α          γ          β    ⟹      α             map
  ▼          ▼          ▼           ▼             ▼
  X ◀──f──── U ──g────▶ Y           X ─────▶ X ⊔_U Y
```

the right-hand square being cartesian as soon as the `γ, g', g, β` square is. -/
lemma isPullback_pushout_map_inl_of_isPullback (H : IsPullback γ g' g β) :
    IsPullback α (pushout.inl f' g') (pushout.inl f g)
      (pushout.map f' g' f g α β γ hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inl_desc _ _ _)
    (pushout_map_preimage_opensRange_inl_of_isPullback f g f' g' α β γ hf hg H)

include hf hg in
/-- For a morphism of spans of open immersions whose `X`-component square is cartesian, the
preimage of the chart `Y` under the induced morphism of pushouts is the chart `Y'`. -/
lemma pushout_map_preimage_opensRange_inr_of_isPullback (H : IsPullback γ f' f α) :
    pushout.map f' g' f g α β γ hf.symm hg.symm ⁻¹ᵁ (pushout.inr f g).opensRange =
      (pushout.inr f' g').opensRange := by
  apply le_antisymm
  · rintro p hp
    have : p ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]
      trivial
    obtain (⟨y', rfl⟩ | hmem) := this
    · replace hp : (pushout.inl f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) y' ∈
          (pushout.inr f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inl_desc] at hp
      obtain ⟨z, hz⟩ := hp
      obtain ⟨u, hu, -⟩ := (pushout_inl_eq_inr_iff f g (α y') z).mp
        (by
          rw [Scheme.Hom.comp_apply] at hz
          exact hz.symm)
      obtain ⟨u', -, rfl⟩ := Scheme.exists_preimage_of_isPullback H u y' hu
      exact ⟨g' u', ((pushout_inl_eq_inr_iff f' g' _ _).mpr ⟨u', rfl, rfl⟩).symm⟩
    · exact hmem
  · rintro p ⟨z', rfl⟩
    change (pushout.inr f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) z' ∈
      (pushout.inr f g).opensRange
    rw [pushout.inr_desc, Scheme.Hom.comp_apply]
    exact ⟨β z', rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `X`-component square is cartesian,
the `Y`-component square of the induced morphism of pushouts is cartesian:

```
  Y' ────▶ X' ⊔_{U'} Y'
  │             │
  β             map
  ▼             ▼
  Y ─────▶ X ⊔_U Y
```
-/
lemma isPullback_pushout_map_inr_of_isPullback (H : IsPullback γ f' f α) :
    IsPullback β (pushout.inr f' g') (pushout.inr f g)
      (pushout.map f' g' f g α β γ hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inr_desc _ _ _)
    (pushout_map_preimage_opensRange_inr_of_isPullback f g f' g' α β γ hf hg H)

end PointsAndMap

end AlgebraicGeometry
