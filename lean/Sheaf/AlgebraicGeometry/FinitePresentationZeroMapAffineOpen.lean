/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Eventual vanishing on one affine open

Source: Stacks Project, Limits, Tag 01ZR (3), first proof, affine case;
Algebra, Tag 05N7 (3), finite-generator argument.
(blueprint: lem-pc-fp-zero-map-affine-open-eventually).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Vanishing on one affine open of the fixed model holds at every sufficiently late stage.
No quasi-compactness of the whole model is needed.
Source: Stacks Project, Limits, Tag 01ZR (3), first proof, affine case;
Algebra, Tag 05N7 (3), finite-generator argument
(blueprint: lem-pc-fp-zero-map-affine-open-eventually).

Proof: restrict to the inverse images of the affine open `U`. They are affine because
all base changes of the affine transition maps are affine. Their coordinate rings
form the directed colimit of the stage coordinate rings: Spec carries ring colimits
to affine limits, the tail is cofinal, and tensoring the coordinate ring of `U`
with the base diagram commutes with colimits. Quasi-coherence identifies the
restrictions and their pullbacks with modules and scalar extension. The source has
finitely many generators. For each generator its image in the target becomes zero
under scalar extension to the limit. Present the target by a finite matrix. Lift
vectors witnessing that these images lie in the relation image from the limit ring
to one stage. The finitely many entries of the resulting differences become zero
at a later common stage, by the elementwise ring-colimit equality criterion.
The map then kills the generators, hence is zero on this affine scheme.
A zero map stays zero after scalar extension, so it is zero at every later stage.
The associated sheaf map is zero on every subopen `W`, as asserted. This argument
also covers the empty affine open, zero modules, and a singleton index preorder. -/
theorem finitePresentation_zero_map_affine_open_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (F G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hF_ft : F.IsFiniteType) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map δ = 0)
    (U : Xi.Opens) (hU : IsAffineOpen U) :
    ∃ (l : I), j ≤ l ∧ ∀ (k : I) (hjk : j ≤ k), l ≤ k →
      ∀ (W : (pullback f (Spec.map
        (R.map (homOfLE (hij.trans hjk))))).Opens),
        W ≤ (pullback.fst f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))) ⁻¹ᵁ U →
        ((Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map δ).app W = 0 := by
  sorry

end AlgebraicGeometry
