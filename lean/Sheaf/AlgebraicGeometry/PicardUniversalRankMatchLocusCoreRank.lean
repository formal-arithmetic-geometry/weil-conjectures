/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore

/-! # The immersion representing universal common-rank matching

Reuse the locally finitely presented rank-match locus and forget the extra property.
Source: Stacks Project, Tag 0BDP.
(blueprint: lem-sc-picard-universal-rank-match-locus-core-rank).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

abbrev PicardUniversalRankMatchCoreCondition {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  PicardUniversalRankMatch f E g

/-- The locally finitely presented rank-match locus also represents the core condition.
Source: Stacks Project, Tags 0BDP, 0B91 and 0BDL.
(blueprint: lem-sc-picard-universal-rank-match-locus-core-rank)

Apply the existing construction of the universal rank-match locus, which gives an
immersion locally of finite presentation without the structure-pushforward hypothesis.
Retain its immersion and factorization equivalence and forget local finite presentation.
The core condition is definitionally the same universal rank-match predicate, so this
is exactly the required universal property, including empty test schemes and rank zero.
-/
theorem exists_picardUniversalRankMatchLocus_core_rank {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatchCoreCondition f E g := by
  have _ := @hO
  obtain ⟨W, j, hj, _, hW⟩ := exists_picardUniversalRankMatchLocus_finitePresentation_core f E
  exact ⟨W, j, hj, fun g ↦ hW g⟩

/-- The corrected core condition and PicardUniversalRankMatch have identical definitions:
both require the two direct images and the pulled-back E to have the same local rank
universally under further base change. Unfolding the two definitions proves the equivalence
by reflexivity; no rank of E is inferred from the ranks of its direct images.
Source: Stacks Project, Tag 0BDP, rank fixed before the two lowest-cohomology loci.
(blueprint: lem-sc-picard-universal-rank-match-locus-core-compat) -/
theorem picardUniversalRankMatchCoreCondition_iff {X S T : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f] (E : X.Modules)
    [E.IsFiniteLocallyFree] (g : T ⟶ S) :
    PicardUniversalRankMatchCoreCondition f E g ↔ PicardUniversalRankMatch f E g := by rfl
end AlgebraicGeometry.Scheme
