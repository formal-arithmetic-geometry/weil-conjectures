/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData

/-! Explicit projection comparison for open tensor support -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The adjoint transpose of the normalized tensor comparison is invertible.

This is the concrete projection-formula comparison on the specified tensor models. Its
source is the extension by zero of `tensorU (M, j* N)` and its target is the ambient tensor
of `j! M` with `N`. The underived localized extension/tensor formula is applied degreewise
on flat-term K-flat representatives; exactness of restriction and extension transports the
result to the derived categories, and the tensor-model representative equations identify the
result with the displayed transpose. The same construction is performed on the vertical
ringed diagram site, so arbitrary semilinear transitions are retained.
Source: Stacks, sites-modules.tex, Tag 0E8I; sites-cohomology.tex, Tags 06YS and 06YU.
(blueprint: lem-sf-open-tensor-support-aux). -/
theorem tensor_open_extension_comparison_isIso {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (M : Der (restrictRing m d.j d.R)) (N : Der d.R) :
    IsIso ((o.opens.adj.homEquiv
      (o.tensorU.functor.obj (M, o.opens.jStar.obj N))
      (o.tensorX.functor.obj (o.opens.jShriek.obj M, N))).symm
      (o.tensorU.functor.map (CategoryTheory.Prod.mkHom
        (o.opens.adj.unit.app M) (𝟙 _)) ≫
        o.tensorComparison.comparison.inv.app (o.opens.jShriek.obj M, N))) := by
  sorry

end SheafOfModules.OpenTensorNormalization
