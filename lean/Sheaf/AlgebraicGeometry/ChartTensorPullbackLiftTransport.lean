/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import Sheaf.AlgebraicGeometry.ChartOrdinaryMapRecovery

/-! # Transporting an ordinary chart lift to tensor pullback coordinates

Source: Stacks Project, Tags 0095 and 0096, functoriality of pullback.
(blueprint: lem-pc-chart-tensor-pullback-lift-transport).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A compatible ordinary chart map gives the canonical tensor chart equation.
Source: Stacks Project, Tags 0095 and 0096, composition and base change of pullback.
(blueprint: lem-pc-chart-tensor-pullback-lift-transport).

Proof: The map v is the unique pullback lift identifying the iterated chart
with the direct chart. Its second projection gives the congruence in d. Replace
all tensor pullbacks by ordinary pullbacks using the unique comparison of left
adjoints to the same pushforward. Under this comparison, tensor composition is
ordinary pullback composition; openCoverTensorPullbackComparison is restriction
followed by that same comparison. The ordinary pullback associativity identity
for v, the two chart projections and the ambient triangle makes the two ways
of composing these comparisons agree. Naturality then moves the ordinary map s
through the stage comparison. Substitute the assumed d equation, cancel adjacent
inverse comparisons, and obtain the displayed equation. This is a coherence
identity only: no finiteness, affinity, directedness or limit is used. -/
theorem chart_tensor_pullback_lift_transport
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (q₀ : Z ⟶ X)
    (w : p ≫ q = q₀) (U : X.OpenCover.{u}) (a : U.I₀)
    (F G : X.Modules)
    (φ : (Scheme.Modules.tensorPullback q₀).obj F ⟶
      (Scheme.Modules.tensorPullback q₀).obj G) :
      let Uk : Y.OpenCover.{u} := U.pullback₁ q
      let V : Z.OpenCover.{u} := Uk.pullback₁ p
      let W : Z.OpenCover.{u} := U.pullback₁ q₀
      let t₀ := Scheme.Modules.openCoverTensorPullbackComparison q₀ U a
      let ψ := t₀.hom.app F ≫ (Scheme.Modules.pullback (W.f a)).map φ ≫ t₀.inv.app G
      ∀ s : (Scheme.Modules.pullback (U.pullbackHom q a)).obj
          ((Scheme.Modules.pullback (U.f a)).obj F) ⟶
        (Scheme.Modules.pullback (U.pullbackHom q a)).obj
          ((Scheme.Modules.pullback (U.f a)).obj G),
        chartOrdinaryMapRecovery q p q₀ w U a
          ((Scheme.Modules.pullback (U.f a)).obj F)
          ((Scheme.Modules.pullback (U.f a)).obj G) ψ s →
        let tq := Scheme.Modules.openCoverTensorPullbackComparison q U a
        let r := tq.inv.app F ≫ s ≫ tq.hom.app G
        let tp := Scheme.Modules.openCoverTensorPullbackComparison p Uk a
        let e := Scheme.Modules.tensorPullbackCompositionIso p q q₀ w
        tp.inv.app ((Scheme.Modules.tensorPullback q).obj F) ≫
            (Scheme.Modules.pullback (Uk.pullbackHom p a)).map r ≫
            tp.hom.app ((Scheme.Modules.tensorPullback q).obj G) =
          (Scheme.Modules.pullback (V.f a)).map
            (e.inv.app F ≫ φ ≫ e.hom.app G) := by sorry

end AlgebraicGeometry
