/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence

/-!

# The square law of the pushforward exchanges

For a commutative square of morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁`,
`φ₁ : P₁ ⟶ M₁`, the pullback exchanges of `φ₀`, `φ₁` and the pushforward exchanges of `ψ`, `ψ'`
satisfy the square law (`NearbyCyclesModel.pushforwardExchange_square_aux`, in abstract
categories)
```
e'^*(χ_ψ) ∘ bc' ∘ Rk'_*(α_{φ₀}) = α_{φ₁}(Rg_*) ∘ Ψ_{P₁}(bc) ∘ χ_{ψ'}(f₀^*),
```
where `bc`, `bc'` are the base change morphisms of the squares of bases and of special fibres.
Consequently `Rk'_*` of the pullback exchange of `φ₀` is invertible at `A` as soon as the other
five maps are invertible at the relevant objects
(`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square`), and the pullback exchange
itself is invertible if moreover `Rk'_*` reflects isomorphisms
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Abstract

variable {DX DX1 DZ DZ1 SX SX1 SZ SZ1 : Type*} [Category DX] [Category DX1] [Category DZ]
  [Category DZ1] [Category SX] [Category SX1] [Category SZ] [Category SZ1]
  {ΨM : DX ⥤ SX} {ΨM1 : DX1 ⥤ SX1} {ΨP : DZ ⥤ SZ} {ΨP1 : DZ1 ⥤ SZ1}
  {f : DX ⥤ DZ} {e : DX1 ⥤ DZ1} {g : DX1 ⥤ DX} {k : DZ1 ⥤ DZ}
  {f' : SX ⥤ SZ} {e' : SX1 ⥤ SZ1} {g' : SX1 ⥤ SX} {k' : SZ1 ⥤ SZ}
  {Rg : DX ⥤ DX1} {Rk : DZ ⥤ DZ1} {Rg' : SX ⥤ SX1} {Rk' : SZ ⥤ SZ1}

end Abstract

section Square

variable {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end Square

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
