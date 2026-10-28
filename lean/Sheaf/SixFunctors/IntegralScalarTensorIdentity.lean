/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! Multiplication normalization of the ordinary scalar/tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- Identity scalar balancing preserves the multiplication unit.
Source: current blueprint lem-coef-integral-finite-extension, final paragraph;
the flat-representative normalization of scalarTensor.
(blueprint: lem-sf-integral-scalar-tensor-identity)

Proof: take flat-term K-flat representatives P and Q. The identity scalar
restriction is the identity on sections, so its conjugate tensorIdentity is
multiplication r tensor x ↦ rx. The inverse balancing map sends
(r tensor x) tensor (s tensor y) to rs tensor (x tensor y).
Both displayed composites therefore send this generator to rx tensor sy.
The same formula holds degreewise on signed total tensors, since the scalars
have degree zero. The universal derived counits give the equality on the
localized representatives. Naturality transports it along representative
isomorphisms to arbitrary K and M. Zero objects and the empty site use the
same calculation. -/
theorem scalarTensor_identity {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel X R) (K M : DerivedCategory (pbcModules X R)) :
    (scalarTensor (𝟙 R) a a).inv.app (K, M) ≫
        (tensorIdentity R).hom.app (a.tensor.obj (K, M)) =
      a.tensor.map (Prod.mkHom ((tensorIdentity R).hom.app K)
        ((tensorIdentity R).hom.app M)) := by sorry

end WeilConjectures.PurCompactSupport
