/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Finitely many ranks on an affine part of the universal rank locus

Source: Stacks Project, Tag 0BDP, first proof paragraph.
(blueprint: lem-sc-picard-universal-rank-match-finite-ranks).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On an affine base open, finitely many fibre ranks cover the universal rank locus.
Source: Stacks Project, Tag 0BDP, rank decomposition paragraph; finite local freeness
and properness give the finite bound even without connected fibres.
(blueprint: lem-sc-picard-universal-rank-match-finite-ranks).

Proof:
1. The inverse image of the affine open is quasi-compact, since f is proper.
   Trivialize E on an open cover of that inverse image, and take a finite subcover.
   Let R be the finite set of ranks of these trivializations, with zero adjoined.
2. At a point s satisfying the universal rank condition, apply that condition to the
   identity of Spec kappa(s) and its unique point. Its nonempty neighbourhood is the
   whole one-point scheme. The third clause gives a constant rank r for E on the fibre;
   pullback along this open inclusion and the identity changes no rank.
3. If the fibre is nonempty, choose a point of it and a member of the finite
   trivializing cover containing its image in X. Pulling both trivializations to its
   residue field and comparing dimensions shows that r is that member's rank, hence
   belongs to R. If the fibre is empty, E on it has rank zero, so choose zero in R.
   This proves the bound without assuming f is surjective or the fibres connected. -/
theorem picardUniversalRankMatch_finiteRanks {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ R : Finset ℕ, ∀ s : S, s ∈ U →
      PicardUniversalRankMatch f E (S.fromSpecResidueField s) →
      ∃ r ∈ R,
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r := by sorry

end AlgebraicGeometry.Scheme
