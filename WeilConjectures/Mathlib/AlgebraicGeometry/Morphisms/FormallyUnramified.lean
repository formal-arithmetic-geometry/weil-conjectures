/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The locus where two morphisms into an unramified scheme agree

Unramified morphisms are *rigid*: two morphisms `a b : T ⟶ W` into a scheme `W` that is
unramified over a base `Z` and that agree after composing with `p : W ⟶ Z` agree on an open
subscheme of `T`, which contains the range of every morphism into `T` equalising them. In
particular two such morphisms that agree at a single point agree on a whole neighbourhood of
that point.

The whole content is Mathlib's `AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal`:
the diagonal `Limits.pullback.diagonal p : W ⟶ W ×[Z] W` of a formally unramified morphism
locally of finite type is an open immersion, and `AlgebraicGeometry.FormallyUnramified.eqLocus`
is the preimage of its range under `Limits.pullback.lift a b h : T ⟶ W ×[Z] W`.

## Main results

- `AlgebraicGeometry.FormallyUnramified.eqLocus` — the open subscheme of `T` on which `a`
  and `b` agree;
- `AlgebraicGeometry.FormallyUnramified.eqLocus_ι_comp_eq` — the two morphisms do agree on it;
- `AlgebraicGeometry.FormallyUnramified.range_subset_eqLocus` — a morphism `c : S ⟶ T` with
  `c ≫ a = c ≫ b` has its range inside it; in particular, if `a` and `b` agree at a point of
  `T` then that point lies in `eqLocus p a b h`.

## Implementation notes

`eqLocus` is stated as a `Scheme.Opens` of `T` rather than as an abstract
`IsOpenImmersion e` with the two properties, or as a `Limits.HasEqualizer a b` together with
`IsOpenImmersion (Limits.equalizer.ι a b)`. The three carry the same information: an open
immersion into `T` with open image is the same thing as an open of `T` up to a unique
isomorphism over `T`, and `eqLocus_ι_comp_eq` together with `range_subset_eqLocus` and the
fact that `Scheme.Opens.ι` is a monomorphism exhibit `(eqLocus p a b h).ι` as an equaliser
of `a` and `b`. The `Scheme.Opens` form is chosen because the intended use —
cofilteredness of the category of pointed étale neighbourhoods of a geometric point — needs
the equaliser as an open of `T`, in order to intersect it with other opens and to transport
it along a closed immersion.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace FormallyUnramified

variable {T W Z : Scheme.{u}} (p : W ⟶ Z) [FormallyUnramified p] [LocallyOfFiniteType p]
  (a b : T ⟶ W) (h : a ≫ p = b ≫ p)

/-- The open subscheme of `T` on which two morphisms `a b : T ⟶ W` agree, for `p : W ⟶ Z`
formally unramified and locally of finite type and `a ≫ p = b ≫ p`.

It is the preimage under `Limits.pullback.lift a b h : T ⟶ W ×[Z] W` of the range of the
diagonal `Limits.pullback.diagonal p`, which is open since `p` is unramified. -/
noncomputable def eqLocus : T.Opens :=
  pullback.lift a b h ⁻¹ᵁ (pullback.diagonal p).opensRange

omit [FormallyUnramified p] [LocallyOfFiniteType p] in
/-- A morphism `c : S ⟶ T` equalising `a` and `b` sends `Limits.pullback.lift a b h` into the
diagonal: the triangle
```
  S ------------- c -------------> T
   \                               |
    \                    pullback.lift a b h
   c ≫ a                           |
      \                            ↓
       -----> W --- diagonal p ---> W ×[Z] W
```
commutes. -/
theorem comp_lift_eq_comp_diagonal {S : Scheme.{u}} (c : S ⟶ T) (hc : c ≫ a = c ≫ b) :
    c ≫ pullback.lift a b h = (c ≫ a) ≫ pullback.diagonal p := by
  refine pullback.hom_ext ?_ ?_ <;> simp [hc]

/-- The range of a morphism `c : S ⟶ T` equalising `a` and `b` is contained in
`eqLocus p a b h`. In particular, if `a` and `b` agree at a point of `T` — that is, after
composing with a morphism from the spectrum of a field — then that point lies in the
agreement locus. -/
theorem range_subset_eqLocus {S : Scheme.{u}} (c : S ⟶ T) (hc : c ≫ a = c ≫ b) :
    Set.range c.base ⊆ (eqLocus p a b h : Set T) := by
  rw [Set.range_subset_iff]
  intro s
  exact ⟨(c ≫ a).base s, by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      comp_lift_eq_comp_diagonal p a b h c hc]⟩

/-- `a` and `b` agree on `eqLocus p a b h`. -/
@[reassoc]
theorem eqLocus_ι_comp_eq : (eqLocus p a b h).ι ≫ a = (eqLocus p a b h).ι ≫ b := by
  have hrange : Set.range ((eqLocus p a b h).ι ≫ pullback.lift a b h).base ⊆
      Set.range (pullback.diagonal p).base := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hfac := IsOpenImmersion.lift_fac (pullback.diagonal p)
    ((eqLocus p a b h).ι ≫ pullback.lift a b h) hrange
  have h₁ := congr($hfac ≫ pullback.fst p p)
  have h₂ := congr($hfac ≫ pullback.snd p p)
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, ← h₂]

/-- If `f : X ⟶ Y` is formally unramified and locally of finite type, then every morphism
`σ : T ⟶ X` whose composite with `f` is an open immersion is itself an open immersion. In
particular a section of `f` over an open of `Y` is an open immersion. -/
theorem isOpenImmersion_of_comp {T X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f] (σ : T ⟶ X) [IsOpenImmersion (σ ≫ f)] : IsOpenImmersion σ := by
  rw [← pullback.lift_snd (f := σ ≫ f) (g := f) (𝟙 T) σ (by simp)]
  have : IsOpenImmersion (pullback.lift (𝟙 T) σ (by simp) : T ⟶ pullback (σ ≫ f) f) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback σ f) inferInstance
  infer_instance

end FormallyUnramified

end AlgebraicGeometry
