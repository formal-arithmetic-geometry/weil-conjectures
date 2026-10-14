/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorGradedProductProjection

/-! # Projection of homogeneous quotient actions

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection-first).
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

/-- Compatibility of the degree-n section obtained from tensorPowSection f 1
on the degree-n(e+1) coefficient.

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, quotient multiplication on the square-zero ideal;
Tag 01XC, naturality of the affine cohomology comparison.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection-first).
Proof: The inclusion i is mono by short exactness, so hlocal uniquely determines the
quotient action. Lift the homogeneous quotient section locally through the degreewise
unit. On each kernel summand k_d, use k_inclusion and b_multiply to compute multiplication
by this lift. Project to degree n(e+2); k_projection gives the diagonal term and
k_orthogonal kills every other input degree. The surviving input degree is
n(e+1). If n=0 this is a diagonal calculation in degree zero; no distinct-degree
assumption is needed. The colimit cofan k determines the map from these summands.
Changing a lift by a kernel section changes no product, since the ideal is square zero.
Restriction compatibility glues these local identities, and hglobal identifies the
resulting global action with mu. Apply H^1 and use haction. Transport the resulting
square through the canonical ideal-kernel, annihilated-module unit, affine cohomology,
and tensor-degree comparisons fixed by hD. Naturality identifies the transported map
with mulTensorPowSection f F e 1;
evaluating gives the stated equation.
The identity holds for every class, including the zero class and zero section. -/
theorem tensorGradedAction_projection_first {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (ρ : T.C.right.obj.obj (op ⊤) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I))
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y)
    (haction : ∀ g : T.C.right.obj.obj (op ⊤), ρ g =
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ g)).hom) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
    let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
    (∀ z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I,
      tensorGradedCoefficientProjection T D (e + 1)
        (ρ (tensorGradedSection T D 0 (tensorPowSection f 1)) z) =
      H.map (mulTensorPowSection f F e 1) (tensorGradedCoefficientProjection T D e z)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
