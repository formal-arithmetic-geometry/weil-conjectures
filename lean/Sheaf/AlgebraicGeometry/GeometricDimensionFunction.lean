/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# Dimension functions defined by immediate geometric specializations

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Definition 2.1.1,
with Expose XIV, Definitions 2.1.1--2.1.2 (blueprint: def-per-geometric-dimension-function).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- An integer-valued dimension function decreases by one along every immediate geometric
specialization. A geometric specialization into `barX` is a geometric point `a` of its
strict localization; it is immediate exactly when the closure of its image has dimension
one. The two evaluations use the underlying points in the original scheme.
Source: ILO XVII, Definition 2.1.1; XIV, Definitions 2.1.1--2.1.2
(blueprint: def-per-geometric-dimension-function). -/
def IsGeometricDimensionFunction (X : Scheme.{u}) (δ : X → ℤ) : Prop :=
  ∀ (Ωx : Type u) [Field Ωx] [IsAlgClosed Ωx] (barX : Spec (.of Ωx) ⟶ X)
    (Ωy : Type u) [Field Ωy] [IsAlgClosed Ωy]
    (a : Spec (.of Ωy) ⟶ strictHenselizationScheme barX),
    topologicalKrullDim
      (closure ({a (IsLocalRing.closedPoint Ωy)} : Set (strictHenselizationScheme barX))) = 1 →
    δ (strictHenselizationStructuralMap barX (a (IsLocalRing.closedPoint Ωy))) =
      δ (barX (IsLocalRing.closedPoint Ωx)) + 1

end AlgebraicGeometry.Scheme
