/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.FormalChartGeometricData

/-! # Completed dimensions from an extended formal model

Source: ILO VI 1.6; Stacks 00MA, 07NY, 07NV.
(blueprint: lem-trf-extended-formal-model-dimensions).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
open FormalChartGeometric

/-- Completed dimensions from an extended formal model.
Source: ILO VI 1.6; Stacks 00MA, 07NY, 07NV.
(blueprint: lem-trf-extended-formal-model-dimensions).

Proof: Unpack the extended model, retaining its coefficient ring D and pair map.
Identify the polynomial ring in zero variables with D[T]. The formal monoid
ring dimension theorem identifies its completed stratum with D and computes its
dimension. In the mixed case quotient the stratum also by eta; its specified image
is a parameter of D, so the same theorem gives a regular stratum and both dimension
drops by one. An algebra equivalence of the stratum with D is canonical on constants,
so it equals the rho of the given model. Transport these assertions through the pair
map, retaining D; these are ModelDimensions. For trivial T the boundary is zero; the same
calculation holds. In coefficient dimension zero the mixed parameter case is empty.
-/
theorem extended_formal_model_dimensions
    (B T : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommMonoid T]
    (_hfs : IsFineSaturatedMonoid T) (_hsharp : ∀ t : T, IsUnit t → t = 1)
    (J : Ideal B) (_hJ : J ≤ IsLocalRing.maximalIdeal B) (mixed : Bool)
    (_hmodel : AddMonoidAlgebra.HasExtendedFormalMonoidModel B (Additive T) J mixed) :
    ModelDimensions B T J mixed := by sorry

end AlgebraicGeometry
