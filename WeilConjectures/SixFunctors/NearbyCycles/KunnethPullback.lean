/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth

/-!

# The Künneth map of nearby cycles and pullbacks

The Künneth map of nearby cycles `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.kunnethMap`) is compatible with the
pullback exchanges `α`: for morphisms of models `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P`
compatible with `φ₁ : P ⟶ M`, `φ₂ : P ⟶ N` and `φ₁' : P' ⟶ M'`, `φ₂' : P' ⟶ N'`, the square
```
Lρ_P'^* (Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B) --Lρ'^* Π--> Lρ_P'^* Ψ_P (A ⊠ B)
        | (α_{ρ_M} ⊗ α_{ρ_N}) ∘ m                     | m ∘ α_{ρ_P}
Le₁'^* Ψ_{M'} Lρ_M^* A ⊗ Le₂'^* Ψ_{N'} Lρ_N^* B --Π--> Ψ_{P'} (Lρ_M^* A ⊠ Lρ_N^* B)
```
commutes up to the tensor and pullback comparisons `m`
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`). It follows from the square law of
the pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) and their monoidality
(`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`). In particular, when the
exchanges `α_ρ` are invertible (e.g. for open immersions,
`WeilConjectures.SixFunctors.NearbyCycles.OpenExchange`), `Lρ_P'^* Π_{A,B}` is invertible if and
only if `Π_{Lρ_M^* A, Lρ_N^* B}` is
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_of_isKunnethRestriction`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### Abstract computation -/

section Abstract

variable {DX DY DZ DXU DYU DZU SX SY SZ SXU SYU SZU : Type*} [Category DX] [Category DY]
  [Category DZ] [Category DXU] [Category DYU] [Category DZU] [Category SX] [Category SY]
  [Category SZ] [Category SXU] [Category SYU] [Category SZU] [MonoidalCategory DZ]
  [MonoidalCategory DZU] [MonoidalCategory SZ] [MonoidalCategory SZU]
  {ΨM : DX ⥤ SX} {ΨN : DY ⥤ SY} {ΨP : DZ ⥤ SZ} {ΨMU : DXU ⥤ SXU} {ΨNU : DYU ⥤ SYU}
  {ΨPU : DZU ⥤ SZU} {f₁ : DX ⥤ DZ} {f₂ : DY ⥤ DZ} {f₁' : SX ⥤ SZ} {f₂' : SY ⥤ SZ}
  {e₁ : DXU ⥤ DZU} {e₂ : DYU ⥤ DZU} {e₁' : SXU ⥤ SZU} {e₂' : SYU ⥤ SZU}
  {ρM : DX ⥤ DXU} {ρN : DY ⥤ DYU} {ρP : DZ ⥤ DZU} {ρM' : SX ⥤ SXU} {ρN' : SY ⥤ SYU}
  {ρP' : SZ ⥤ SZU} [ρP.OplaxMonoidal] [ρP'.OplaxMonoidal]

end Abstract

/-! ### The compatibility -/

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
