/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!

# The pullback exchange of a restriction of the generic fibre

Let `N` be a model of `X` with special fibre `X'`, let `g : G ⟶ N.generic` and `e : G ⟶ X` with
`g ≫ N.ε = e`, and let `M` be the model with the same total space and special fibre as `N`, with
generic fibre `G`, `j_M = g ≫ j_N` and `ε_M = e`. For a morphism of models `φ : M ⟶ N` over the
identities with identity morphism of total spaces and morphism of generic fibres `g`, the pullback
exchange `α_φ : L(𝟙)^* Ψ_N ⟶ Ψ_M L(𝟙)^*` is the image under `Li^* Rj_{N*}` of the unit of
`Lg^* ⊣ Rg_*`, up to the canonical identifications `L(𝟙)^* ≅ 𝟭`, `Rj_{N*} Rg_* ≅ R(g ≫ j_N)_*`
and `Lg^* Lε_N^* ≅ L(g ≫ ε_N)^*`
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`).

The base change morphism of the square of generic fibres is computed by the abstract mate lemma
`CategoryTheory.mateEquiv_app_of_isoId_comp`.

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

variable {X Y Z : Scheme.{u}}

end Squares

namespace NearbyCyclesModel

variable {X X' G : Scheme.{u}}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
