/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleChartCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleChartPullback
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Tensor pullback preserves quasi-coherence on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03GA; Modules on Sites,
Tags 03DO, 03DF and 03DN (blueprint: lem-sfb-space-module-pullback-quasicoherent).

The pullback is the existing left adjoint of the chart-limit module direct image.
Quasi-coherence is the existing local-presentation predicate on the small étale site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Tensor pullback along any morphism of algebraic spaces preserves quasi-coherence.
Source: Stacks Project, Properties of Spaces, Tag 03GA, using Modules on Sites,
Tags 03DO, 03DF and 03DN (blueprint: lem-sfb-space-module-pullback-quasicoherent).

Proof:
Choose local presentation data for M. The scheme charts lying over the charts of
these data cover X, by `moduleChart_coversTop`. For every such commuting triangle,
`moduleTensorPullback_chart_functor` supplies a left adjoint between the localized
module categories, identifies its structure module, and compares it naturally with
restriction of `moduleTensorPullback f`. A left adjoint preserves colimits, so
Mathlib's `Presentation.map` transports the given presentation on the target chart.
Transport along the comparison isomorphism gives a presentation of the restricted
pullback on the source chart. These presentations and the covering are exactly
`SheafOfModules.QuasicoherentData`, which implies the required predicate.
No finiteness of the presentations or flatness of the morphism is used. -/
theorem isQuasicoherent_moduleTensorPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((moduleTensorPullback f).obj M).IsQuasicoherent := by
  classical
  obtain ⟨P⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  refine SheafOfModules.QuasicoherentData.isQuasicoherent
    { I := Σ i, ModuleChart f (P.X i)
      X := fun p ↦ p.2.left
      coversTop := moduleChart_coversTop f P.X P.coversTop
      presentation := ?_ }
  intro p
  apply Classical.choice
  obtain ⟨hY, hX, F, hF, ⟨e⟩, ⟨c⟩⟩ :=
    moduleTensorPullback_chart_functor f (P.X p.1) p.2
  let := hY
  let := hX
  let := hF
  exact ⟨((P.presentation p.1).map F e).ofIsIso (c.app M).hom⟩

end AlgebraicGeometry.AlgebraicSpace
