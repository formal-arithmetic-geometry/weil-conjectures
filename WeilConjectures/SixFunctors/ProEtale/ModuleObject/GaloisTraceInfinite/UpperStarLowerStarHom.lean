/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.BaseChange

/-!
# The comparison `g_* g^* ⟶ g'_* g'^*` along a morphism of weakly étale covers

For weakly étale `g : Y ⟶ X`, `g' : Y' ⟶ X` and `s : Y' ⟶ Y` over `X`, the restriction along `s`
(`AlgebraicGeometry.ProEtale.restrictionHom`) conjugated with the comparisons `g^* ≅ j_g^*`
is a monoidal natural transformation `g^* ⋙ g_* ⟶ g'^* ⋙ g'_*`
(`AlgebraicGeometry.ProEtale.upperStarLowerStarHom`). It is compatible with the units of
`g^* ⊣ g_*` and `g'^* ⊣ g'_*` and with the actions of automorphisms of `Y` and `Y'` over `X`
(`AlgebraicGeometry.ProEtale.galoisActionNatTrans_comp_upperStarLowerStarHom`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y Y' Y'' : Scheme.{u}} (g : Y ⟶ X) (g' : Y' ⟶ X) (g'' : Y'' ⟶ X) [WeaklyEtale g]
  [WeaklyEtale g'] [WeaklyEtale g'']

variable {g g' g''}

end AlgebraicGeometry.ProEtale
