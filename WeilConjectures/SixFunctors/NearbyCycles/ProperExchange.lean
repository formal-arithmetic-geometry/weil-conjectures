/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.Adjunction.MatePasting

/-!

# The pushforward exchange of nearby cycles through base change morphisms

Let `φ : M ⟶ N` be a morphism of models (`NearbyCyclesModel.Hom`) over `f : X ⟶ Y` and
`f' : X' ⟶ Y'`, with morphism `t` of total spaces and `g` of geometric generic fibres. The
pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` (`NearbyCyclesModel.Hom.pushforwardExchange`) is
the mate of the pullback exchange, which is the pasting of the squares of identifications, of
geometric generic fibres and of special fibres. Its component at `K` is therefore the composite
(`NearbyCyclesModel.Hom.pushforwardExchange_app`)
```
Li_N^* Rj_{N*} Lε_N^* Rf_* K ⟶ Li_N^* Rj_{N*} Rg_* Lε_M^* K      (base change of the ε-square)
  ⟶ Li_N^* Rt_* Rj_{M*} Lε_M^* K                                (composition of direct images)
  ⟶ Rf'_* Li_M^* Rj_{M*} Lε_M^* K                               (base change of the special fibres)
```
as in the proof of blueprint `det-sp-nearby-cycles-exchanges` (2). The middle arrow
(`NearbyCyclesModel.Hom.lowerStarExchange`) is the iterated mate of the pullback comparison of the
square of geometric generic fibres, hence invertible. So `χ_f` is invertible at `K` as soon as the
two base change morphisms are
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isIso_baseChangeMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel.Hom

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
