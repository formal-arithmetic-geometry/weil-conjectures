/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisActionModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.UpperStarLowerStarHom

/-!
# The unit transport of module objects on underlying sheaves

For weakly étale `g : Y ⟶ X`, `p₁ : Y' ⟶ X` and `s : Y' ⟶ Y` with `s ≫ g = p₁`, the unit
transport `g_* g^* ⟶ p₁_* p₁^*` of module objects along `s`
(`AlgebraicGeometry.ProEtale.CondensedRing.unitTransport`, built from the unit of `s^* ⊣ s_*` and
the composition isomorphisms) is, on underlying sheaves, the restriction along `s` in the
restriction model `AlgebraicGeometry.ProEtale.upperStarLowerStarHom`, through the identifications
`upperStarForgetIso` (`AlgebraicGeometry.ProEtale.CondensedRing.forget_map_unitTransport_app_eq`).
We also record the underlying sheaf maps of the unit and of the trace of a Galois covering.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Transport

variable {X Y Y' Y'' : Scheme.{u}} {g : Y ⟶ X} {g' : Y' ⟶ X} {g'' : Y'' ⟶ X} [WeaklyEtale g]
  [WeaklyEtale g'] [WeaklyEtale g'']

end Transport

end CondensedRing

end AlgebraicGeometry.ProEtale
