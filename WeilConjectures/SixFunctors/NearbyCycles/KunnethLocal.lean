/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!

# The Künneth map of nearby cycles is local on the special fibre

Let `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` be the Künneth map of nearby cycles
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.kunnethMap`). This file shows that
its invertibility is local on the special fibre of `P`: if every point of the special fibre has an
open neighbourhood `W` over which `M`, `N`, `P` restrict to models `M'`, `N'`, `P'` along open
immersions of the total spaces with cartesian squares of geometric generic fibres
(`NearbyCyclesModel.IsKunnethRestriction`), such that the Künneth map
`Π_{Lρ_M^* A, Lρ_N^* B}` of the restrictions is invertible, then `Π_{A,B}` is invertible
(`NearbyCyclesModel.isIso_kunnethMap_of_forall_exists_restriction`).

Indeed the pullback exchanges of open immersions are invertible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`), so the compatibility of the
Künneth map with pullbacks (`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) identifies
`Π_{A,B}|_W` with `Π_{Lρ_M^* A, Lρ_N^* B}` up to isomorphisms; and a morphism of the derived
category of a noetherian scheme is invertible if it is so on the members of an open cover
(`ProEtale.CondensedRing.isIso_of_forall_exists_isIso_upperStar_map`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Invertibility is local -/

section Local

variable {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]

end Local

namespace NearbyCyclesModel

/-! ### Restrictions of products -/

variable {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
