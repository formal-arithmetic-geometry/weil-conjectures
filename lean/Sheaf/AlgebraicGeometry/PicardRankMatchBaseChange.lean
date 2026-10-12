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
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus

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

Proof: Work locally on T where the common rank is r. The rank hypothesis includes every
further base change, so the same rank-r condition holds on every open restriction and
every test scheme over that restriction. The perfect derived direct images supplied by
Tag 0B91 have local finite-free models beginning in degree zero. Apply Tag 0BDL to each:
the universal rank-r condition means the structure morphism factors through the locus.
At each image point, the residue-field test gives degree-zero fibre dimension r.
Choose the residue model used in the proof of Tag 0BDL, with no negative terms and
a rank-r first term; cancel contractible summands before making this choice.
In this model the locus is cut out by the outgoing degree-zero matrix entries.
On this locus degree-zero cohomology
is the first free term. After any base change it remains that term tensored with the new
structure sheaf. The canonical cohomology base-change morphism is therefore the identity
on this scalar extension, and is invertible. Under the degree-zero direct-image comparison,
this is the ordinary base-change map: its adjoint is the composite of the tensor-pullback
unit and pushforward-composition comparisons defining moduleBaseChangeMap. This follows
from naturality of the comparison and the adjunction triangle identities, rather than
from existence of an arbitrary isomorphism between the objects. Apply this to E and its
dual. Open restriction of the canonical map agrees with the map in the restricted square;
isomorphisms of sheaves are local, so these local conclusions prove invertibility globally.
The rank-zero first term gives a zero-to-zero isomorphism. On an empty base the argument
is vacuous. The structure-sheaf unit hypothesis is not needed for this implication.
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
  by sorry

end AlgebraicGeometry.Scheme
