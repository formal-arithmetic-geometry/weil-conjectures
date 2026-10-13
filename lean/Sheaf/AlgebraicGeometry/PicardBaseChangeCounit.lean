/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Counit formula for the canonical Picard base-change map

Source: Stacks Project, Tags 0095, 0096, 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The square comparison from the bottom composite pullback to the top composite.
Source: Stacks Project, Tags 0095 and 0096, composition of module pullbacks.
(blueprint: lem-sc-picard-base-change-counit) -/
noncomputable def picardBaseChangeSquareIso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (A : W.Modules) :
    (tensorPullback (Limits.pullback.snd f (h ≫ j))).obj ((tensorPullback h).obj A) ≅
      (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.snd f j)).obj A) :=
  picardTensorCompIso (Limits.pullback.snd f (h ≫ j)) h A ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj A)
      (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_snd])) ≪≫
    (picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.snd f j) A).symm

/-- Identify the iterated top pullback of a coefficient with its pullback to X_T.
Source: Stacks Project, Tags 0095 and 0096, composition of module pullbacks.
(blueprint: lem-sc-picard-base-change-counit) -/
noncomputable def picardBaseChangeCoefficientIso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules) :
    (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≅
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M :=
  picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.fst f j) M ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
      (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_fst]))

/-- The adjoint of the canonical base-change map for one coefficient.
Source: Stacks Project, Tag 08HY, mate description; Tags 0095 and 0096,
composition comparisons. (blueprint: lem-sc-picard-base-change-counit)

Proof: Express the map as the mate of the pushforward square, as in its definition.
Take its transpose along p_T. Naturality of the top unit and the bottom counit,
and the two adjunction triangle identities, give the square pullback comparison
followed by the pullback of the p_W counit. To identify the comparison, transport
all four tensor pullbacks to ordinary pullbacks by leftAdjointUniq. Its unit and
counit equations identify the transported mate with the ordinary pullback square;
ordinary pullback composition is conjugate to sectionwise pushforward composition.
Transport back to obtain picardBaseChangeSquareIso. Finally naturality of the
p_T counit moves the coefficient comparison out of the pushed-forward factor,
giving the final coefficient isomorphism. This argument is for an arbitrary
module M and involves no evaluation, tensor pairing, or invertibility of the
base-change map; it applies also to zero modules and empty schemes. -/
theorem picardDirectImageBaseChangeMap_counit
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules) :
    (tensorPullback (Limits.pullback.snd f (h ≫ j))).map
        (picardDirectImageBaseChangeMap f j h M) ≫
      (Classical.choose (exists_tensorPullbackAdjunction
        (Limits.pullback.snd f (h ≫ j)))).counit.app
          ((tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M) =
    (picardBaseChangeSquareIso f j h
      ((pushforward (Limits.pullback.snd f j)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M))).hom ≫
      (tensorPullback (picardBaseChangeTop f j h)).map
        ((Classical.choose (exists_tensorPullbackAdjunction
          (Limits.pullback.snd f j))).counit.app
            ((tensorPullback (Limits.pullback.fst f j)).obj M)) ≫
      (picardBaseChangeCoefficientIso f j h M).hom := by sorry

end AlgebraicGeometry.Scheme.Modules
