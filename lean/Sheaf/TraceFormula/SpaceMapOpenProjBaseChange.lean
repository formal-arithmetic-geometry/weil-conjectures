/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.TraceFormula.SpaceLineModuleProjInput

/-! # Descent of open immersions along relative-Proj base change

Source: Stacks Project, Tags 0D3C, 0D2Z and 01O9
(blueprint: lem-trf-space-map-open-proj-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An arbitrary map into relative Proj is an open immersion if its compatible local
maps over an etale base cover are open immersions. No graded evaluation is required.

Source: Stacks, Descent on Spaces, Tag 0D3C, open-immersion descent sentence; Spaces and
Morphisms, Tag 03M4 (blueprint: lem-trf-space-map-open-proj-base-change).

Proof: PullbackData.isPullback identifies each local relative Proj P_i with P times_T T_i.
The projections P_i to P are etale and cover P, by base change of the given etale family.
For a test scheme W to P, apply hcover to W to T and use the scheme pullback to lift its
covering arrows into the P_i; this gives exactly the fppf-local lifting cover predicate.
The structural equation of r and hmap give a commutative square X_i to P_i over X to P.
Paste it with the Cartesian square P_i to T_i over P to T. The exterior square is hcart,
so pullback cancellation makes the first square Cartesian. Thus the pullback of r over
P_i is represented by r_i, an open immersion by assumption. Apply open-immersion etale
locality on the scheme target. For an index family in a larger universe, refine the
etale cover of each affine target chart by finitely many affine source opens, and then
unite these finite families over the small affine basis; this yields a small covering
family with the same local open-immersion property. This applies to the empty target
and to empty covering families without choosing a point. -/
theorem space_map_open_proj_base_change
    (S : Scheme.{u}) (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T) (A : T.left.GradedAlgebraData)
    (I : Type v) (Tᵢ Xᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hget : ∀ i, Etale (g i).left)
    (hcover : ∀ (V : Over S) (x : V ⟶ T),
      ∃ R : Sieve V.left, R ∈ Scheme.fppfTopology V.left ∧
        ∀ (W : Over S) (a : W ⟶ V), R a.left →
          ∃ (i : I) (b : W ⟶ Tᵢ i), b ≫ g i = a ≫ x)
    (k : ∀ i, yoneda.obj (Xᵢ i) ⟶ X.obj.obj) (fᵢ : ∀ i, Xᵢ i ⟶ Tᵢ i)
    (hcart : ∀ i, IsPullback (k i) (yoneda.map (fᵢ i)) f (yoneda.map (g i)))
    (Aᵢ : ∀ i, (Tᵢ i).left.GradedAlgebraData)
    (D : ∀ i, Scheme.GradedAlgebraData.PullbackData (g i).left A (Aᵢ i))
    (r : X.obj.obj ⟶ yoneda.obj (projOver T A))
    (hstruct : ∀ (W : Over S) (a : X.obj.obj.obj (op W)),
      (r.app (op W) a).left ≫ A.relProjHom = (f.app (op W) a).left)
    (rᵢ : ∀ i, Xᵢ i ⟶ projOver (Tᵢ i) (Aᵢ i))
    (hmap : ∀ (i : I) (W : Over S) (a : W ⟶ Xᵢ i),
      (a ≫ rᵢ i).left ≫ (D i).relProjComparison =
        (r.app (op W) ((k i).app (op W) a)).left)
    (hopen : ∀ i, IsOpenImmersion (rᵢ i).left) :
    IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) r := by sorry

end AlgebraicGeometry.AlgebraicSpace
