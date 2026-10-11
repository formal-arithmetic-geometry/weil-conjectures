/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Descent of finite relations among module maps

Source: Stacks Project, Limits, Lemma 32.10.2 (Tag 01ZR)
(blueprint: lem-pc-fp-relation-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite relations between descended module maps hold at a later stage.
Source: Stacks Project, Limits, Tag 01ZR (blueprint: lem-pc-fp-relation-descent).

The modules are the given models on `X_j`; the modules on `X` are their canonical
base changes. Transport through the specified model isomorphisms preserves equality.
For each relation, `lhs k` and `rhs k` are its two composites on the chosen models.
Functoriality of tensor pullback identifies their images with the pulled-back composites.
The finite type `M` indexes the finite collection of modules (`[Finite M]`).

Proof, following the four steps of the node:
1. Keep the finitely many modules and maps occurring in the composites. The given
   models already descend them. If identifications must first be aligned, apply
   part (2) of `lem-pc-fp-module-map-descent` to maps between the fixed models and
   increase the stage to make all composites maps between those models.
2. For one equality, subtract the two composites to obtain a map whose pullback
   to `X` is zero. Tensor pullback is additive and preserves composition.
   Since `Xi` is quasi-compact, choose a finite affine cover. At any later stage
   its inverse images are affine and cover; a sheaf map vanishes if it vanishes
   on these opens. Noetherianity is retained from the node but is unused here.
3. By `lem-weil-pbc-spec-colimit-limit`, the limit ring is the directed colimit
   of the stage rings. On each affine of `Xi`, tensoring its coordinate ring
   with these rings gives the affine coordinate rings of the base changes,
   and tensor product commutes with colimits. Choose finite generators of the
   source module and a finite free presentation `P` of the target. Lift the
   images of the generators to vectors in the target's finite free module.
   Their vanishing in the limit cokernel means they equal `P` times vectors
   over the limit ring. Lift all entries of these vectors to a common stage
   using clause (1) of `lem-pc-filtered-colimit-commrings-elementwise`. The
   finitely many entries of the resulting differences vanish at a later common
   stage by clause (2), compared with zero. Hence all generators map to zero,
   and the difference map vanishes on this affine at that stage.
4. Directedness gives one stage above the finitely many stages needed for the
   affines and relations. Vanishing persists under further pullback, and the
   affine cover then shows that every specified equality holds on `X_j'`. -/
theorem finiteRelation_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : Type u) [Finite M]
    (Fj : M → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hFj_fp : ∀ k : M, (Fj k).IsFinitePresentation)
    (hFj_qc : ∀ k : M, (Fj k).IsQuasicoherent)
    (n : ℕ) (src tgt : Fin n → M)
    (lhs rhs : ∀ k : Fin n, Fj (src k) ⟶ Fj (tgt k))
    (hrel : ∀ k : Fin n,
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (lhs k) =
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (rhs k)) :
    ∃ (j' : I) (hjj' : j ≤ j'),
      ∀ k : Fin n,
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (lhs k) =
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (rhs k) := by
  sorry

end AlgebraicGeometry
