/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Continuity of base change for the small sites

Base change along an arbitrary morphism is continuous for the small `Q`-topologies of
`P`-schemes, for `Q ≤ P`: it preserves covers because covers are jointly surjective
families of `Q`-morphisms and the base change square is cartesian, and it preserves
compatible families because it is representably flat, the small site being finitely
complete.

## Main results

- `AlgebraicGeometry.Scheme.coverPreserving_overPullback`: base change along an arbitrary
  morphism preserves the covering sieves of the small `Q`-topologies.
- `AlgebraicGeometry.Scheme.isContinuous_overPullback`: base change along an arbitrary
  morphism is continuous for the small `Q`-topologies.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` preserves the covering sieves of
the small `Q`-topologies of `P`-schemes, for `Q ≤ P`.

Both squares below are cartesian, so a point `x` of `V ×_U W` and a preimage `w` of its
image in `V` under a covering morphism `φ.left` are jointly a point of `V' ×_U W`:

```
  V' ×_U W ──(Over.pullback P ⊤ g).map φ──→ V ×_U W ──────→ W
      │                                        │            │
      │ pullback.fst V'.hom g                  │ fst V.hom g│ g
      ↓                                        ↓            ↓
      V' ───────────── φ.left ──────────────→ V ──V.hom──→ U
```
-/
lemma coverPreserving_overPullback (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    CoverPreserving (U.smallGrothendieckTopology Q (Q := P))
      (W.smallGrothendieckTopology Q (Q := P)) (MorphismProperty.Over.pullback P ⊤ g) where
  cover_preserve {V S} hS := by
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP] at hS
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology W hQP]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun x ↦ ?_
    obtain ⟨V', φ, w, hSφ, hφl, hφw⟩ := hS (pullback.fst V.hom g x)
    have h := MorphismProperty.Over.isPullback_map_left g φ
    obtain ⟨ξ, -, hξ⟩ := Scheme.exists_preimage_of_isPullback h w x hφw
    exact ⟨_, (MorphismProperty.Over.pullback P ⊤ g).map φ, ξ,
      ⟨V', φ, 𝟙 _, hSφ, (Category.id_comp _).symm⟩, Q.of_isPullback h hφl, hξ⟩

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is continuous for the small
`Q`-topologies of `P`-schemes, for `Q ≤ P`. -/
theorem isContinuous_overPullback (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) (coverPreserving_overPullback P Q hQP g)

end AlgebraicGeometry.Scheme
