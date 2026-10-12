/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus

/-! # Rank and evaluation for a module pulled back from the base

Source: Stacks Project, Tag 0BDP, projection-formula paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A module pulled back from a finite locally free base module satisfies the universal
rank condition, and its canonical evaluation map is invertible. This implication does
not construct or represent any locus. Source: Stacks Project, Tag 0BDP, paragraph using
Tag 01E8 (the projection formula for finite locally free modules).
(blueprint: lem-sc-picard-pullback-evaluation)

Proof: Put p = X_T → T and q = X_T → X. The projection formula and the unit isomorphism
at O_T give p_*p^*N ≅ N ⊗ p_*O_X_T ≅ N. This identification is the adjunction unit at N:
check on an open where N is finite free, where the unit is a finite direct sum of the
unit at O_T. Consequently this unit is invertible. The triangle identity then makes
the counit at p^*N invertible. Naturality transports invertibility along the supplied
isomorphism q^*E ≅ p^*N. The direct image of q^*E is thus isomorphic to N and is finite
locally free. After any further base change h : T' → T, pull back the supplied
isomorphism through the cartesian-square identifications, obtaining q'^*E ≅ p'^*h^*N.
Dualizing commutes with pullback for finite locally free modules, so the same assertion
holds for the dual and h^*N^dual. Apply the projection formula using the hypothesis at
h ≫ g to identify the two direct images with h^*N and its dual. On a neighbourhood U of
each point t of T', choose a frame of h^*N of finite rank r; its dual has the dual frame
of the same rank. Pulling that frame up to X_U shows that q_U^*E also has rank r. These
are exactly the three rank assertions in PicardDirectImageRankCondition. Finally the
canonical base-change maps are isomorphisms: under the projection-formula identifications
they are the identity on the pullback of N and its dual, as follows from their defining
adjunction units. This gives the remaining conjunct for every h. The empty
base has no points to check, and finite free rank zero uses the empty frame. -/
theorem picard_rankCondition_and_isIso_counit_of_pullback {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    PicardDirectImageRankCondition f E g ∧
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).counit.app
          ((Modules.tensorPullback (pullback.fst f g)).obj E)) := by
  sorry

end AlgebraicGeometry.Scheme
