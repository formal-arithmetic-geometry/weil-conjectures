/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.TensorHomogeneousKernelAction

/-! # Coefficient coordinates for homogeneous ideal multiplication

Source: Stacks Project, Tag 09MS, tensor powers in the graded ideal sequence;
Tag 01CD, monoidal pullback of modules.
(blueprint: lem-sc-tensor-ideal-section-coefficient-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] canonicalTensorBoundaryComparisons
noncomputable section

/-- Coefficient-degree coordinates turn raw ideal multiplication into multiplication
by f on the last tensor-power factor. This is solely a monoidal comparison on Z:
no graded algebra, ideal action, kernel, pushforward, or cohomology map occurs.
Source: Stacks Project, Tag 09MS, tensor powers; Tag 01CD, tensor pullback.
(blueprint: lem-sc-tensor-ideal-section-coefficient-comparison).
Proof: Substitute the canonical comparisons for D using hD. Expand the
section-degree comparison as boundaryPullbackPowIso followed by tensorPowMulIso,
and the coefficient-degree comparison as its three explicit factors. Naturality
of boundaryPullbackTensorIso moves the section through the pullback tensorator.
The definition tensorPowSection f 1 is f followed by the inverse right unitor;
its extra unit factor cancels the degree-one tensorPowMulIso. The inverse
coefficient comparison then groups the ideal factor and the first n factors,
followed by e blocks of n factors. Raw multiplication appends one further block
of n factors. This is exactly mulTensorPowSection f F e 1. To check the grouping
identity, induct on e and on n in boundaryPullbackPowIso and tensorPowMulIso;
the successor steps use tensorator naturality and the associator pentagon, and
the zero steps use the unit comparison and the triangle identity. Naturality
of the associators leaves the ideal factor unchanged, so it need not be
invertible. The arithmetic equality h identifies the two output degrees and
proof irrelevance makes the result independent of its proof. In particular n=0
and e=0 use the same unit and associativity identities, without a positivity
assumption. -/
theorem tensorIdealSectionMultiply_coefficient_comparison {X Z : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (hI : j.ker ^ 2 = ⊥) (n : ℕ) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D) (e : ℕ)
    (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (h : n * (e + 1) + n * (0 + 1) = n * ((e + 1) + 1)) :
    tensorIdealSectionMultiply j L (n * (0 + 1)) (n * (e + 1))
        (n * ((e + 1) + 1)) h (tensorPowSection f 1 ≫ (D.a 0).inv) =
      (boundaryCoefficientDegreeIso j L n e).hom ≫
        mulTensorPowSection f ((tensorPullback j).obj
          (j.ker.toModules ⊗ L.tensorPow n)) e 1 ≫
        (boundaryCoefficientDegreeIso j L n (e + 1)).inv := by sorry

end
end AlgebraicGeometry.Scheme.Modules
