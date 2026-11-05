/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingSections

/-!
# Base change of the coefficient sheaves on weakly contractible objects

Let `f : X ⟶ Y` be a morphism of schemes, `k_Y : Y ⟶ Spec ℤ` and `Λ` a condensed abelian group.
The morphism `η : k_Y^* p^* Λ ⟶ f_* (f ≫ k_Y)^* p^* Λ` adjoint to the composition isomorphism of
the pullbacks (`AlgebraicGeometry.ProEtale.unitCompUpperStarCompInv`) is, on sections over an
object `V` of `Y_proét` whose sections of the coefficient sheaves are computed by `π₀`
(`AlgebraicGeometry.ProEtale.bijective_unit_app_comp_map_unit`), the map
`Λ(π₀ V) ⟶ Λ(π₀(X ×_Y V))` induced by the projection `X ×_Y V ⟶ V`
(`AlgebraicGeometry.ProEtale.map_unit_comp_unitCompUpperStarCompInv_app`). Hence it is bijective
as soon as `π₀(X ×_Y V) ⟶ π₀(V)` is a homeomorphism, i.e. as soon as morphisms `V ⟶ Spec LC(S, ℤ)`
and `X ×_Y V ⟶ Spec LC(S, ℤ)` correspond
(`AlgebraicGeometry.ProEtale.bijective_unitCompUpperStarCompInv_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Compat

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) {X Y : Scheme.{u}} (f : X ⟶ Y)
  (kY : Y ⟶ specZ.{u})

variable (V : Y.ProEt)

end Compat

end AlgebraicGeometry.ProEtale
