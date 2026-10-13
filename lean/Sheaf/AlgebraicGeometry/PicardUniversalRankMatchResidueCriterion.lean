/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel

/-! # Residue-field criterion for universal Picard rank matching

Source: Stacks Project, Tag 0BDP, second and third proof paragraphs, and Tag 0BCD.
(blueprint: lem-sc-picard-universal-rank-match-residue-criterion).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- For a fixed-rank fibre, universal rank matching is tested by its two ordinary
residue-field direct images. Empty fibres satisfy universality independently of r.
Source: Stacks Project, Tag 0BDP, second and third proof paragraphs (perfect direct
images and arbitrary base change), and Tag 0BCD (minimal finite-free residue models).
(blueprint: lem-sc-picard-universal-rank-match-residue-criterion).

Proof:
1. If X_s is empty, every further pullback is empty. Both ordinary direct images
   are zero and finite locally free of rank zero. The pullback of E on the empty
   scheme has rank zero, so the universal condition holds using the whole open.
2. Suppose X_s is nonempty. If the universal condition holds, test it on the
   identity of Spec kappa(s). The open neighbourhood of its unique point is the
   whole spectrum. Its chosen rank equals r, since E has rank r and the fibre has
   a point. Thus both ordinary direct images have rank r.
3. Conversely suppose those direct images have rank r. Perfect direct image and
   arbitrary base change for E and E dual identify them with degree-zero derived
   fibres. Over the field choose minimal finite-free models (Tag 0BCD): they have
   no negative terms, their degree-zero terms have rank r, and every differential
   is zero. In particular their outgoing degree-zero differentials are zero.
4. Pulling these models to any scheme over Spec kappa(s) keeps those differentials
   zero and computes ordinary direct images by derived base change. Their degree-zero
   cohomology is free of rank r, and pullback preserves the constant rank r of E.
   Restricting to the whole open gives the universal condition at every point.
   Composition of pullback squares identifies these modules with the ones in the
   definition of PicardUniversalRankMatch. -/
theorem picardUniversalRankMatch_residue_iff {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) (s : S)
    (hEr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r) :
    PicardUniversalRankMatch f E (S.fromSpecResidueField s) ↔
      IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u}) ∨
        (SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
            ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E)) r ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
            ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj
              (Modules.dual E))) r) := by
  sorry

end AlgebraicGeometry.Scheme
