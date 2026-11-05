/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The change of geometric generic fibre and the unit of `Lg^* ⊣ Rg_*`

Let `φ : M ⟶ N` be a morphism of models and `φ.toCartesian : M ⟶ φ.cartesianModel` the change of
geometric generic fibre of its cartesian factorization (`NearbyCyclesModel.Hom.toCartesian`): the
identity on total spaces, and `g = φ.toCartesian.generic : 𝒳_η̄ ⟶ 𝒴_η̄ ×_𝒴 𝒳` on geometric generic
fibres. Its pullback exchange is, up to isomorphisms, `Li^* Rj'_*` applied to the unit
`G ⟶ Rg_* Lg^* G` of the adjunction `Lg^* ⊣ Rg_*`; it is a split monomorphism at `C` as soon as
this unit is a split monomorphism at `G = Lε'^* C`
(`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit`).

The abstract input (`Adjunction.isSplitMono_mateEquiv_app_of_isSplitMono_unit`) is a statement
about mates: for adjunctions `L_N ⊣ R_N`, `L_M ⊣ R_M`, `L_G ⊣ R_G`, a functor `T ≅ 𝟭` and an
isomorphism `θ : T ⋙ L_M ≅ L_N ⋙ L_G`, the mate `R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ` is a split
monomorphism at `y` as soon as the unit of `L_G ⊣ R_G` is.

The file also collects the formal closure properties of the class of morphisms whose unit is
split at a given complex:

* the unit of an adjunction `L ⊣ R` is a split monomorphism at `G` as soon as `G` is a retract of
  some `R H` (`CategoryTheory.Adjunction.isSplitMono_unit_app_of_retract`);
* split units compose
  (`ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp`,
  `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp₃`);
* the unit of a universal homeomorphism is an isomorphism (topological invariance,
  `isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism`);

and their consequence for a change of geometric generic fibre `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂`
universal homeomorphisms
(`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_factor₃`).

These statements were in `TraceFormula.Specialization.NearbySliceInvariants`,
`NearbySliceInvariantsUnit` and `NearbySliceFactorisationUnit`; they are collected here, below
the slice step of Deligne's finiteness theorem, so that the invariance of nearby cycles under
change of trait can use them.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {D E F : Type*} [Category D] [Category E] [Category F]
  {LN : D ⥤ E} {RN : E ⥤ D} {LM : D ⥤ F} {RM : F ⥤ D} {LG : E ⥤ F} {RG : F ⥤ E}
  (adjN : LN ⊣ RN) (adjM : LM ⊣ RM) (adjG : LG ⊣ RG) {T : D ⥤ D}

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

end NearbyCyclesModel

namespace NearbyCyclesModel

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
