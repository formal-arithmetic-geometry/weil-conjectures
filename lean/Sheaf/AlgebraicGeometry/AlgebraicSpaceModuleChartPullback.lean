/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule

/-!
# Tensor pullback on commuting scheme-chart triangles

Source: Stacks Project, Modules on Sites, Tags 03D7, 03DF, 04J0 and 04J1;
Properties of Spaces, Tags 03G8 and 03GA
(blueprint: lem-sfb-space-module-chart-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A chart triangle induces a left adjoint on localized module categories, carrying
structure modules to structure modules and commuting with global tensor pullback.
Source: Stacks Project, Modules on Sites, Tags 04J0, 04J1, 03D7 and 03DF;
Properties of Spaces, Tag 03G8
(blueprint: lem-sfb-space-module-chart-pullback).

Proof: each small étale slice is equivalent to the small étale site of its
scheme chart. The affine étale basis of that scheme has a small skeleton in the
section universe, so its additive sheafification exists and preserves finite
limits. Transport along the slice equivalence gives both displayed sheafification
properties. Identify these slices with the corresponding localized enlarged ringed
sites. Base change first localizes the
ringed morphism at `V`; the chart `q` gives a further étale localization on the
source. Compose its module tensor pullback with this restriction and transport
back through the scheme-object equivalences. Call the resulting functor `F`.
Each factor is left adjoint by the module adjunction or the ringed equivalence,
so `F` is left adjoint. Tensor pullback sends the structure module A to B:
`b ⊗ a ↦ b * image(a)` and `b ↦ b ⊗ 1` are inverse by balancing, and induce
inverse sheaf maps after sheafification. Restriction and the ringed equivalences
also preserve the structure module. This gives the displayed unit isomorphism.
The pullback-localization comparison identifies the composite on `M.over V`
with the restriction to `q.left` of enlarged tensor pullback of M. The chart-limit
comparison identifies its right adjoint with `moduleDirectImage f`; uniqueness
of left adjoints identifies it with `moduleTensorPullback f`. These comparisons
are natural in every module M, giving the displayed natural isomorphism.
No quasi-coherence, covering condition on a chart, or flatness is required. -/
theorem moduleTensorPullback_chart_functor {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : Y.EtaleSite)
    (q : ModuleChart f V) :
    HasSheafify (Y.etaleTopology.over V) AddCommGrpCat.{u} ∧
      HasSheafify (X.etaleTopology.over q.left) AddCommGrpCat.{u} ∧
      ∃ F : SheafOfModules.{u} (Y.structureSheaf.over V) ⥤
        SheafOfModules.{u} (X.structureSheaf.over q.left),
      F.IsLeftAdjoint ∧
      Nonempty (SheafOfModules.unit (X.structureSheaf.over q.left) ≅
        F.obj (SheafOfModules.unit (Y.structureSheaf.over V))) ∧
      Nonempty (SheafOfModules.overFunctor Y.structureSheaf V ⋙ F ≅
        moduleTensorPullback f ⋙ SheafOfModules.overFunctor X.structureSheaf q.left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
