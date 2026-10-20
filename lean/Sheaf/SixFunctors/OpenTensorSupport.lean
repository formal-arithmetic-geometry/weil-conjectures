/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData
import Sheaf.SixFunctors.OpenTensorSupportAux

/-! # Tensoring objects extended from an open -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- Tensoring an object extended from the open with any derived object remains
in the essential image of extension by zero. No projection map is chosen here.

Proof: the localized module extension/tensor formula identifies
j!(P tensor j*Q) with j!P tensor Q. Apply this isomorphism in each bidegree.
Extension by zero is a left adjoint and hence preserves the direct sums in the
total complex. Naturality makes the comparison commute with each differential,
including the sign on the second differential. Thus it is a chain isomorphism.
Extension by zero preserves K-flatness: tensor it with an acyclic complex E and
use that same total comparison, exactness of restriction, K-flatness on the open,
and exactness of extension. It preserves flat terms by the underived comparison
and the exactness criterion for tensoring a flat module. Restriction preserves
the resolving class as well. Resolve both input objects by flat-term K-flat
complexes; the total chain comparison therefore computes both derived tensors.
The representative comparisons in `TensorModel` transport it to the supplied
models, giving an isomorphism from the ambient tensor to extension of a derived
object on the open. This proves precisely the stated essential-image membership.
Apply the argument on the vertical diagram site for arbitrary coefficient systems;
no passage to levelwise derived categories or flat transition hypothesis is used.

Source: Stacks, sites-modules.tex, Tag 0E8I;
sites-cohomology.tex, Tags 0GL1, 06YS and 06YU.
(blueprint: lem-sf-open-tensor-support). -/
theorem derivedTensor_openSupported {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (M : Der (restrictRing m d.j d.R)) (N : Der d.R) :
    o.opens.jShriek.essImage (o.tensorX.functor.obj (o.opens.jShriek.obj M, N)) := by
  let f := (o.opens.adj.homEquiv
      (o.tensorU.functor.obj (M, o.opens.jStar.obj N))
      (o.tensorX.functor.obj (o.opens.jShriek.obj M, N))).symm
      (o.tensorU.functor.map (CategoryTheory.Prod.mkHom
        (o.opens.adj.unit.app M) (𝟙 _)) ≫
        o.tensorComparison.comparison.inv.app (o.opens.jShriek.obj M, N))
  have hf : IsIso f := tensor_open_extension_comparison_isIso o M N
  let _ : IsIso f := hf
  exact Functor.essImage.ofIso (asIso f) (o.opens.jShriek.obj_mem_essImage _)

end SheafOfModules.OpenTensorNormalization
