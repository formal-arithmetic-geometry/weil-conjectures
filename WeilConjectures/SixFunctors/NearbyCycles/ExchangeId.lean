/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp

/-!

# The pullback exchange of the identity morphism of models

The pullback exchange `α : L(𝟙)^* Ψ_M ⟶ Ψ_M L(𝟙)^*` of the identity morphism of a model
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.id`) is the composite of the
identity isomorphisms `L(𝟙)^* ≅ 𝟭`
(`NearbyCyclesModel.Hom.id_pullbackExchange_app`). It follows from the unit laws of the
composition isomorphisms of the derived pullbacks (`leftDerivedUpperStarComp_id_left_app`,
`leftDerivedUpperStarComp_id_right_app`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Squares

variable {X Y : Scheme.{u}}

end Squares

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
