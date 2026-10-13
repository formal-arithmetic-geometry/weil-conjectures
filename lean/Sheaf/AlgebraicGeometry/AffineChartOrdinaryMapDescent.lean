/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ChartOrdinaryMapRecovery
import Sheaf.Algebra.FinitePresentationColimit

/-! # Ordinary Hom descent on an affine chart

Source: Stacks Project, Tags 01ZR and 05N7 (2).
(blueprint: lem-pc-affine-chart-ordinary-map-descent).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary pullback maps of two fixed modules on one affine chart descend.
Source: Stacks Project, Tag 01ZR, affine proof; Tag 05N7 (2).
(blueprint: lem-pc-affine-chart-ordinary-map-descent).

Proof: Work on the upper tail of j and its partial-order quotient. The stage
charts are the pullbacks of the affine chart along maps between affine bases,
so are affine, including the limit chart. Pullback pasting identifies their rings
with the chart ring tensored over R(j) with R(k); at the limit this is the filtered
colimit of the stage rings. Under the affine quasi-coherent module equivalence,
M and N give finitely presented modules and ordinary pullback is scalar extension.
Apply the map clause of finitePresentation_descent_directedColimit and transport
its map back to sheaves. The pure-tensor equations characterize its comparisons
as ordinary pullback composition. The pullback lift v compares the iterated limit
chart with the direct limit chart, so this gives precisely the displayed equation
with d. The tail contains j; quotienting a preorder does not change its colimit.
Zero rings, empty affine charts and zero modules obey the same tensor argument.
Only chart modules occur here: tensor pullbacks of ambient sheaves and the
comparison with ambient restriction are handled separately. -/
theorem affine_chart_ordinary_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    (M N : (U.X a).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent)
    (hN : N.IsFinitePresentation) (hNq : N.IsQuasicoherent)
    (ψ : (Scheme.Modules.pullback
          (U.pullbackHom (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj M ⟶
        (Scheme.Modules.pullback
          (U.pullbackHom (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj N) :
    ∃ (k : I) (hjk : j ≤ k),
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
      let q₀ := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      let w : p ≫ q = q₀ := by
        rw [← baseChangeMap_comp]
        congr 1
        ext
        simpa using c.w (homOfLE hjk).op
      ∃ s : (Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
          (Scheme.Modules.pullback (U.pullbackHom q a)).obj N,
        chartOrdinaryMapRecovery q p q₀ w U a M N ψ s := by sorry

end AlgebraicGeometry
