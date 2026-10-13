/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PicardCupProductMap
import Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit

/-! # The local dual-basis criterion for degree-zero cup product

Source: Stacks Project, Tag 0BDP, final paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a single base, cup product detects the evaluation counit when the direct image
and the bundle have the same local rank. Neither properness nor flatness nor universal
base-change compatibility is an assumption of this local calculation.

Source: Stacks Project, Tag 0BDP, final paragraph, the two displayed dual bases.
(blueprint: lem-sc-picard-cup-product-local-dual-bases)

Proof: Put p = X_W → W, q = X_W → X, M = q^*E and N = p_*M. Around a point of W,
shrink to an open U on which N is free of rank r and M on X_U has rank r, using
hRanks. The tensor-pullback comparisons identify restriction of the adjunction
counit with the map p_U^*N_U → M_U taking each basis vector to its section.
If the cup transpose is invertible, its inverse takes the coordinate functionals
of the basis of N_U to sections of p_*q^*(E^dual) on U. Pullback commutes with the
finite locally free dual, so these are functionals on M_U. By picardPushforwardPairing_counit,
their products with the basis sections
are delta_ij:
applying the structure-sheaf unit sends their cup product back to evaluation.
Thus the functionals give a left inverse to the restricted counit. On stalks this
is a split injection between free modules of rank r over a commutative local ring.
Its square matrix has a left inverse, hence its determinant is a unit, so it is
invertible. The resulting inverses glue, proving the forward implication.
Conversely an invertible counit identifies M with p^*N. Dualizing this identification
and using the finite locally free projection formula with the structure-sheaf unit
identifies p_*q^*(E^dual) with N^dual. In these identifications the cup product is
ordinary evaluation: adjunction takes a section to its evaluation section, and the
inverse structure unit takes this scalar back to O_W. Its transpose is therefore
invertible. Rank zero uses empty matrices and the zero sheaf; an empty base has
an empty covering, so the assertion still holds. -/
theorem picardCupProduct_isIso_iff_counit_of_local_ranks
    {X S W : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) [E.IsFiniteLocallyFree]
    (j : W ⟶ S)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hN : ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj E)).IsFiniteLocallyFree)
    (hRanks : ∀ w : W, ∃ U : W.Opens, w ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f j)).obj
            ((Modules.tensorPullback (pullback.fst f j)).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ j))).obj E) r) :
    IsIso (picardCupProductMap f E j hO) ↔
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).counit.app
          ((Modules.tensorPullback (pullback.fst f j)).obj E)) := by sorry

end AlgebraicGeometry.Scheme
