/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PicardBaseChangeStalkRanks
import Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.RingTheory.FiniteType

/-! # Canonical base change under universal rank matching

Source: Stacks Project, Tags 0BDP and 0BDL
(blueprint: lem-sc-picard-rank-match-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Universal rank matching forces the two canonical ordinary base-change maps to be
invertible. This asserts no representability or existence of a locus.
Source: Stacks Project, Tag 0BDP, the omitted base-change detail in the third paragraph;
Tag 0BDL, the lowest-cohomology pullback clause; Tag 0B91, arbitrary derived base change.
(blueprint: lem-sc-picard-rank-match-base-change)

Proof: Fix a further base change h. Treat E and its dual using the same stalk argument.
The stalk-rank comparison gives finite generation of the target stalk and a linear
embedding of the source stalk into it (in fact a linear equivalence). The local
lowest-cohomology calculation gives surjectivity of the canonical map on this stalk.
Mathlib's Orzech property for commutative rings now gives injectivity as well, without
any Noetherian hypothesis. The source library's stalk criterion turns bijectivity at
all points into invertibility of the sheaf morphism. Apply this argument separately to
E and its dual. The geometric calculations, including compatibility with the adjoint
that defines the canonical map, are the two named intermediate statements. Rank zero
is included, and the stalk criterion is vacuous on an empty base.
-/
theorem picardRankMatch_baseChange {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) :
  ∀ {T' : Scheme.{u}} (h : T' ⟶ T),
    IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
      (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
      pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj E)) ∧
    IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
      (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
      pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj (Modules.dual E))) :=
  by
    intro T' h
    have hbc (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
        IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
          (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
          pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj F)) := by
      apply Modules.isIso_of_bijective_stalkLinearMap
      intro t
      obtain ⟨hfinite, ⟨e⟩⟩ := picardRankMatch_baseChange_stalk_ranks f E g hR h F hF t
      have := hfinite
      exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap _ e.injective
        (picardRankMatch_baseChange_stalk_surjective f E g hR h F hF t)
    exact ⟨hbc E (Or.inl rfl), hbc (Modules.dual E) (Or.inr rfl)⟩

end AlgebraicGeometry.Scheme
