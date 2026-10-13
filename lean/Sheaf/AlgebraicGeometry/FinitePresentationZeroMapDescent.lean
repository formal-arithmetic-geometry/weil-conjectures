/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Eventual vanishing of one finitely generated module map

Source: Stacks Project, Limits, Tag 01ZR (3), affine vanishing argument.
(blueprint: lem-pc-fp-zero-map-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A map from a finite type quasi-coherent model to a finitely presented model
which vanishes on the inverse limit vanishes at some finite stage.
Source: Stacks Project, Limits, Tag 01ZR (3), affine vanishing argument
(blueprint: lem-pc-fp-zero-map-descent).

Proof: the quasi-compactness of `f` over an affine base makes `Xi` quasi-compact.
Choose finitely many affine opens covering `Xi`. Their inverse images in every stage
and in the limit are affine and cover. On each such open write the source module
with finitely many generators and the target as the cokernel of a finite matrix `P`.
The coordinate rings of these opens form a filtered colimit: Spec turns the ring
colimit into the given affine limit, and tensoring with the coordinate ring of the
open commutes with colimits. Lift the images of the source generators to vectors
in the target's finite free presentation. Their images at the limit lie in the
image of `P`; lift the finitely many coefficients witnessing this to one stage.
Each entry of the difference between the lifted vector and `P` times its witness
is zero in the colimit. The elementwise filtered-colimit criterion makes all these
finitely many entries zero at a later stage. Thus the map kills every generator
on this affine. Choose a common upper bound for the finitely many affines;
vanishing persists under tensor pullback, so the sheaf map vanishes there globally.
Only finite type of the source is needed. Neither Noetherianity of the rings nor
finite presentation or quasi-separatedness of `f` is used. The zero source, zero
target, empty scheme and a singleton directed index set satisfy the same argument. -/
theorem finitePresentation_zero_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) [QuasiCompact f]
    (j : I) (hij : i ≤ j)
    (F G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hF_ft : F.IsFiniteType) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map δ = 0) :
    ∃ (j' : I) (hjj' : j ≤ j'),
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
        (Over.homMk (Spec.map (R.map (homOfLE hjj')))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map δ = 0 := by
  sorry

end AlgebraicGeometry
