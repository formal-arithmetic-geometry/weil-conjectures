/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus

/-! # The evaluation-isomorphism open inside the rank-matched locus

Source: Stacks Project, Tag 0BDP, cup-product and determinant paragraphs.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Inside a simultaneous rank-matched direct-image locus, invertibility of evaluation
is represented by a quasi-compact open immersion, rather than another locally closed
rank stratum. Source: Stacks Project, Tag 0BDP, final two proof paragraphs.
(blueprint: lem-sc-picard-evaluation-open-locus)

Proof: Work locally on W where the common rank is r. The hypotheses explicitly
give finite local freeness of the two direct images of rank r and invertibility of their
canonical base-change maps. Thus their formation commutes with arbitrary base change. The
structure-pushforward isomorphism identifies the
pushforward of evaluation with a cup-product pairing N ⊗ D → O_W, for N the direct image
of E and D the direct image of its dual. Both bundles have rank r. The determinant of
the associated map D → N^dual cuts out a retrocompact open: in local frames it is one
principal open, and frame changes multiply its equation by a unit. These opens glue,
and their inclusion k is quasi-compact. On any test scheme, a perfect pairing supplies
local dual bases of N and D. Regard these bases as sections of E and its dual. Their
products form the identity matrix, so they give inverse maps between E and the pullback
of N: one composite is the identity by the pairing, and a split map between free modules
of the same finite rank is invertible, proving the other composite too. This identifies
the isomorphism as the adjunction counit. Conversely an invertible counit identifies E
with the pullback of N; the projection formula and the structure-pushforward hypothesis
then identify D with N^dual and the cup product with the evaluation pairing, so its
determinant is a unit. All these identifications commute with base change. Thus the
principal-open factorization criterion, valid over arbitrary rings including rings with
nilpotents, gives exactly the asserted equivalence. For rank zero the determinant is 1
and both modules and evaluation are zero, so the whole component is retained. -/
theorem exists_picardEvaluationOpenLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree]
    {W : Scheme.{u}} (j : W ⟶ S)
    (hW : ∀ {T : Scheme.{u}} (h : T ⟶ W), PicardDirectImageRankCondition f E (h ≫ j)) :
    ∃ (Z : Scheme.{u}) (k : Z ⟶ W), IsOpenImmersion k ∧ QuasiCompact k ∧
      ∀ {T : Scheme.{u}} (h : T ⟶ W),
        (∃ l : T ⟶ Z, l ≫ k = h) ↔
          IsIso ((Classical.choose
            (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).counit.app
              ((Modules.tensorPullback (pullback.fst f (h ≫ j))).obj E)) := by
  sorry

end AlgebraicGeometry.Scheme
