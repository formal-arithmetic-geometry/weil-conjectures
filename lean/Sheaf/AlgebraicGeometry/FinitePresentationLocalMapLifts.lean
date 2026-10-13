/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
import Sheaf.Algebra.FinitePresentationColimit

/-! # Affine local lifts of fixed-model maps

Source: Stacks Project, Limits, Tag 01ZR, first proof.
(blueprint: lem-pc-fp-local-map-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local components of a map lift on a finite affine cover at one stage.
This statement imposes no overlap equations on the lifted components.
Source: Stacks Project, Limits, Tag 01ZR, first proof, affine map lifting;
Algebra, Tag 05N7 (2).
(blueprint: lem-pc-fp-local-map-lifts).

Proof: Choose a finite affine cover of Xj, using quasi-compactness over Spec Rj.
Its inverse images at later stages and at the limit are affine. On a chart,
quasi-coherent sheaves and pullback identify with modules and scalar extension.
The stage coordinate rings have colimit the limit chart ring: they are tensor
products of the fixed chart ring with the stage base rings, and tensor products
commute with this colimit. Apply the map clause of finitePresentation_descent_directedColimit
on each chart, passing through the partial-order quotient of the directed preorder.
There are finitely many charts; choose a common upper bound and pull the local maps
there. Composition comparisons transport their scalar-extension equations to the
displayed recovery equations. The comparison e is explicitly the canonical tensor
pullback composition comparison, so no choice of comparison is needed. No agreement
on overlaps has been imposed. Empty charts have unique maps; an empty cover requires
no lifts and j itself is an upper bound. The zero ring and zero modules cause no
exception. Noetherianity is not used. -/
theorem exists_finitePresentation_local_map_lifts
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
          let p := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
          let V := U.pullback₁ p
          ∃ r : ∀ a, (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
            ∀ a,
              let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
              t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
                (U.pullbackHom p a)).map (r a) ≫ t.hom.app (A.obj Gj) =
              (Scheme.Modules.pullback (V.f a)).map
                (e.inv.app Fj ≫ φ ≫ e.hom.app Gj)) := by
  sorry

end AlgebraicGeometry
