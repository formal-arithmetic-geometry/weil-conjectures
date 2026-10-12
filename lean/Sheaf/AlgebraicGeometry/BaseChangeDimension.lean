/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.DimensionAffineOpenCover
import Sheaf.AlgebraicGeometry.DimensionBaseChange
import Sheaf.AlgebraicGeometry.BaseChangeConventions

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Dimension is preserved by scalar extension along algebraically closed fields.

Source: blueprint `lem-sc-base-change-curve`, dimension paragraph; Stacks Tags 00P3
(finite type algebras under field extension) and 04MU (dimension on open covers).

Proof: Put `g = Spec(k') → Spec(k)` and let `p : C ×[Spec(k)] Spec(k') → C` be the
first projection. If `C` is empty then its pullback is empty, since `p` maps into `C`;
both topological Krull dimensions are bottom. Otherwise `g` is surjective: its target
has one point and its source is nonempty. Surjectivity survives base change, so `p`
is surjective and the pullback is nonempty.

Choose an affine open cover `U i ≅ Spec(A i)` of `C`. Since `f` is locally of finite
type, each `A i` is a finite type `k`-algebra. The inverse images `p⁻¹(U i)` form an
affine open cover of the pullback: restriction of a fibre product to an open is the
fibre product of the restriction, and the fibre product of affine spectra is
`Spec(A i ⊗[k] k')`. By the first clause of `dim_base_change` (00P3), the tensor
product and `A i` have equal ring Krull dimensions, including zero rings. Apply
`Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover` to both nonempty schemes;
the equalities on every chart identify their suprema. Finally apply
`Scheme.dim_eq_topologicalKrullDim` on both schemes to get the asserted equality.
Thus the empty scheme and both zero- and one-dimensional curves are included.
(blueprint: base-change-dimension) -/
theorem baseChange_dim {k k' : Type u} {C : Scheme.{u}} [Field k] [Field k']
    [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    (f : C ⟶ Spec (.of k)) [IsCurve f] :
    topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}) =
      topologicalKrullDim C := by
  sorry

end AlgebraicGeometry
