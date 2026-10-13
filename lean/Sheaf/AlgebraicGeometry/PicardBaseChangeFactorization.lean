/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Factorization of the canonical coefficient base-change map

Source: Stacks Project, Tags 0097 and 08HY.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical base change postcomposes the square mate with the coefficient comparison.
Source: Stacks Project, Tag 08HY, base-change construction; Tag 0097, composition.
(blueprint: lem-sc-picard-base-change-factorization)

Proof: Substitute the assumed equality for I. The hom of a composite isomorphism is
its two homs composed. The first is the tensor-pullback composition comparison;
the second transports along v q_W = q_T, proved by the first projection identity
of the pullback lift defining v. These are exactly the coefficient morphism in
picardDirectImageBaseChangeMap. Its preceding factor is moduleBaseChangeMap for
the square v p_W = p_T h. Proof irrelevance identifies the proofs of these two
projection equations with the proofs in the canonical map's definition. This
proves the factorization. The argument does not use a counit, conjugation, a
cartesian-square isomorphism criterion, or nonzero coefficients, and applies to
empty schemes and zero modules as well. -/
theorem picardDirectImageBaseChangeMap_factorization
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules)
    (I : (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≅
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M)
    (hI : I = (picardTensorCompIso (picardBaseChangeTop f j h)
        (Limits.pullback.fst f j) M ≪≫
      eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
        (show picardBaseChangeTop f j h ≫ Limits.pullback.fst f j =
            Limits.pullback.fst f (h ≫ j) from by
          dsimp [picardBaseChangeTop]
          rw [Limits.pullback.lift_fst])))) :
    picardDirectImageBaseChangeMap f j h M =
      moduleBaseChangeMap (Limits.pullback.snd f j)
        (Limits.pullback.snd f (h ≫ j)) h (picardBaseChangeTop f j h)
        (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_snd])
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≫
      (pushforward (Limits.pullback.snd f (h ≫ j))).map I.hom := by sorry

end AlgebraicGeometry.Scheme.Modules
