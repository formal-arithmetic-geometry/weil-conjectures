/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder

/-!

# Continuity of base change for the small sites

Base change along an arbitrary morphism is continuous for the small `Q`-topologies of
`P`-schemes, for `Q ≤ P`: it preserves covers because covers are jointly surjective
families of `Q`-morphisms and `Q` is stable under base change, and it preserves
compatible families because it is representably flat, the small site being finitely
complete.

## Main results

- `CategoryTheory.GrothendieckTopology.coverPreserving_overPullback_smallGrothendieckTopology`:
  base change along an arbitrary morphism preserves the covering sieves of the small
  `Q`-topologies.
- `CategoryTheory.GrothendieckTopology.representablyFlat_overPullback`: base change is
  representably flat, the small site of `P`-schemes being finitely complete.
- `CategoryTheory.GrothendieckTopology.isContinuous_overPullback`: base change along an
  arbitrary morphism is continuous for the small `Q`-topologies.

-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` preserves the covering sieves of
the small `Q`-topologies of `P`-schemes, for `Q ≤ P`: covers are jointly surjective
families of `Q`-morphisms, joint surjectivity is preserved by base change since points lift
through the pullback-pasting isomorphism `V' ×_V (V ×_U W) ≅ V' ×_U W`, and the base change
of a `Q`-morphism is a `Q`-morphism. -/
lemma coverPreserving_overPullback_smallGrothendieckTopology (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    CoverPreserving (U.smallGrothendieckTopology Q (Q := P))
      (W.smallGrothendieckTopology Q (Q := P)) (MorphismProperty.Over.pullback P ⊤ g) where
  cover_preserve {V S} hS := by
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP] at hS
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology W hQP]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun x => ?_
    obtain ⟨V', φ, w, hSφ, hφl, hφw⟩ := hS (pullback.fst V.hom g x)
    -- The base change of `φ` is, up to the pullback-pasting isomorphism, the base change of
    -- `φ.left` along `pullback.fst V.hom g`.
    have hcomp : (pullbackRightPullbackFstIso V.hom g φ.left ≪≫
        pullback.congrHom (MorphismProperty.Over.w φ) rfl).hom ≫
          ((MorphismProperty.Over.pullback P ⊤ g).map φ).left =
        pullback.snd φ.left (pullback.fst V.hom g) := by
      apply pullback.hom_ext
      · simp [pullback.condition]
      · simp
    have hmap : Q ((MorphismProperty.Over.pullback P ⊤ g).map φ).left := by
      have h : Q (pullback.snd φ.left (pullback.fst V.hom g)) := Q.pullback_snd _ _ hφl
      rw [← hcomp] at h
      exact (Q.cancel_left_of_respectsIso _ _).mp h
    -- Lift `x` through the base change of `φ` via `V' ×_V (V ×_U W) ≅ V' ×_U W`.
    obtain ⟨ξ, hξ₁, hξ₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := φ.left) (g := pullback.fst V.hom g) w x hφw
    refine ⟨(MorphismProperty.Over.pullback P ⊤ g).obj V',
      (MorphismProperty.Over.pullback P ⊤ g).map φ,
      (pullbackRightPullbackFstIso V.hom g φ.left ≪≫
        pullback.congrHom (MorphismProperty.Over.w φ) rfl).hom ξ,
      ⟨V', φ, 𝟙 _, hSφ, (Category.id_comp _).symm⟩, hmap, ?_⟩
    exact ((Scheme.Hom.comp_apply _ _ _).symm.trans (by rw [hcomp]; rfl)).trans hξ₂

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is representably flat: the small
site of `P`-schemes over `U` has finite limits and base change preserves them. -/
instance representablyFlat_overPullback (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {W U : Scheme.{u}} (g : W ⟶ U) :
    RepresentablyFlat (MorphismProperty.Over.pullback P ⊤ g) :=
  flat_of_preservesFiniteLimits _

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is continuous for the small
`Q`-topologies of `P`-schemes, for `Q ≤ P`: it preserves covers because covers are jointly
surjective families of `Q`-morphisms and `Q` is stable under base change, and it preserves
compatible families because it is representably flat, the small site being finitely
complete. -/
theorem isContinuous_overPullback (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
    (coverPreserving_overPullback_smallGrothendieckTopology P Q hQP g)

end CategoryTheory.GrothendieckTopology
