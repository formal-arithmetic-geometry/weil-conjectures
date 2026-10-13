/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import Sheaf.Algebra.FinitePresentationColimit

/-! # Local finite-presentation descent data

Source: Stacks Project, Limits, Tag 01ZR, first proof.
(blueprint: lem-pc-fp-local-map-datum).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local maps between fixed models descend compatibly on a cover.
Source: Stacks Project, Limits, Tag 01ZR, first proof, map descent on overlaps.
(blueprint: lem-pc-fp-local-map-datum).

Proof: Choose a finite affine cover at stage j. Descend the restrictions of the
map using Tag 05N7. Cover pairwise intersections by finitely many affine opens;
the equality clause of 05N7 makes the descended maps agree on these overlaps
at a common later stage. These local maps and overlap equations form a morphism
psi of descent data on the pulled-back stage cover U. On the limit cover, the
local maps recover the prescribed map. The associativity comparison of pullbacks
is the conjugate of pushforward composition under the canonical tensor adjunctions.
Thus any map alpha with these components satisfies the displayed equality after
restriction to the limit cover. This is a condition on local components only:
no global stage map is constructed or asserted here. Further base changes preserve
all equations. Empty opens and an empty scheme use the unique local maps.
Finite presentation supplies finite generators and relations; quasi-separatedness
supplies finite overlap covers. Noetherianity is unnecessary. -/
theorem exists_finitePresentation_local_map_datum
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj,
      ∃ (j' : I) (hjj' : j ≤ j'),
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
        ∃ e : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A ⋙ B,
          e = Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (Over.homMk (Spec.map (R.map (homOfLE hjj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjj').op) ∧
        ∃ U : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u},
          Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
          let Q := modulesPseudofunctor.toDescentData U.f
          let V := U.pullback₁ (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
          ∃ ψ : Q.obj (A.obj Fj) ⟶ Q.obj (A.obj Gj),
            ∀ α : A.obj Fj ⟶ A.obj Gj, Q.map α = ψ →
              ∀ a, (Scheme.Modules.pullback (V.f a)).map (e.hom.app Fj ≫ B.map α) =
                (Scheme.Modules.pullback (V.f a)).map (φ ≫ e.hom.app Gj)) := by
  sorry

end AlgebraicGeometry
