/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus
import Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux

/-! # The cup-product criterion for the Picard evaluation map

Source: Stacks Project, Tag 0BDP, final two proof paragraphs.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The direct image of the dual is finite locally free, and the transpose of cup
product detects invertibility of evaluation after every base change. This assertion
concerns a map of two specified modules on W, and constructs no representing locus.
Source: Stacks Project, Tag 0BDP, final two proof paragraphs.
(blueprint: lem-sc-picard-cup-product-criterion)

Proof: Put p = X_W -> W, q = X_W -> X, N = p_*q^*E and D = p_*q^*(E^dual).
The rank condition gives, around every point of W, a common finite rank r for N, D
and E on the corresponding family. The resulting local trivializations show that D
is finite locally free; N is already explicitly finite locally free in the condition.
Pullback commutes with duals of finite locally free modules. Apply pushforward to the
evaluation q^*E tensor q^*(E^dual) -> O_{X_W} and compose cup product with the inverse
of O_W -> p_*O_{X_W}, supplied by hO. Transpose this pairing to obtain φ : D -> N^dual.
The canonical base-change maps in hW identify the pullbacks of N and D with the
corresponding direct images on every test scheme T. Naturality of the adjunction,
evaluation, and the structure-module unit identifies h^*φ with the transpose of the
same cup product on T, including for iterated pullbacks (use the canonical composition
isomorphisms). If this transpose is invertible, choose local dual bases σ_i and τ_j
with cup products δ_ij. View these as sections upstairs. The σ_i give the adjunction
counit p_T^*N_T -> q_T^*E, and the τ_j give a left inverse. Both bundles have rank r,
so in local frames the left-inverse matrices are square and have unit determinant;
they are inverse matrices. Thus the counit is invertible. Conversely an invertible
counit identifies q_T^*E with p_T^*N_T. Dualizing and applying the finite locally free
projection formula gives D_T = N_T^dual tensor p_{T*}O_{X_T} = N_T^dual. Under this
identification the cup product is ordinary evaluation, whose transpose is invertible.
All maps used are the adjoint-defined canonical maps, so the equivalence is for the
displayed chosen adjunction, not merely for an arbitrary isomorphism of its objects.
In rank zero both the pairing transpose and the counit are maps between zero modules
and hence invertible. On the empty base all the assertions are vacuous. -/
theorem exists_picardCupProductCriterion {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree]
    {W : Scheme.{u}} (j : W ⟶ S)
    (hW : ∀ {T : Scheme.{u}} (h : T ⟶ W), PicardDirectImageRankCondition f E (h ≫ j)) :
    ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))).IsFiniteLocallyFree ∧
    ∃ φ : ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))) ⟶
      Modules.dual ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj E)),
      ∀ {T : Scheme.{u}} (h : T ⟶ W),
        IsIso ((Modules.tensorPullback h).map φ) ↔
          IsIso ((Classical.choose
            (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).counit.app
              ((Modules.tensorPullback (pullback.fst f (h ≫ j))).obj E)) := by
  have hD := picard_dual_directImage_isFiniteLocallyFree f hO E j hW
  refine ⟨hD, ?_⟩
  exact picard_cupProductCriterion_of_finiteLocallyFree f hO E j hW hD

end AlgebraicGeometry.Scheme
