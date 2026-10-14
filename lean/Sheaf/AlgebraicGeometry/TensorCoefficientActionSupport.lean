/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorGradedProductProjection

/-! # Homogeneous action has the expected degree support

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-tensor-coefficient-action-support).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

/-- A homogeneous quotient section of degree n carries the d-th ideal summand
into the (n+d)-th ideal summand. No coefficient transport or projection is asserted.
Source: Stacks Project, Tag 09MS, graded ideal sequence; Tag 0B8S, quotient action.
(blueprint: lem-sc-tensor-coefficient-action-support).
Proof: Locally lift the section represented by f along the epimorphic unit in degree n,
using the canonical section-degree comparison. Multiply this lift by the inclusion
of a section of the degree-d kernel. The equation b_multiply places the product in
degree n+d. Its image under the unit is zero, by naturality of the unit and the
kernel equation for the second factor, so it factors uniquely through the degree
n+d kernel. The equation b_quotient identifies the quotient of the lift with the
specified homogeneous section, while hlocal and k_inclusion identify the resulting
map into I with the given action. Two lifts differ by a kernel section; their
products with the ideal section agree by squareZero. Thus the kernel-valued maps
agree on overlaps and glue to v. The hrestrict and hglobal identities identify
v followed by k with the global action. The construction works in degree zero
with the tensor unit, including n=d=0. -/
theorem tensorGradedCoefficient_action_support {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (d : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    ∃ v : kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
        kernel (tensorGradedUnit j (L.tensorPow (n + d))),
      T.k d ≫ μ (tensorGradedSection T D 0 (tensorPowSection f 1)) =
        v ≫ T.k (n + d) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
