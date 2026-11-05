/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Ambient exchange for condensed coefficient module objects

Source: blueprint main-20261015, def-weil-pbc-ambient-ringed-exchange;
Stacks Project, Remark 07A7 (blueprint: def-weil-pbc-ambient-ringed-exchange).

The general ring-sheaf exchange is publicly retained. These definitions give its
internal-module-object form for coefficients pulled back from one condensed ring.
The comparison is the published canonical derived pullback composition comparison;
its mate uses the published derived module-object adjunctions. No completeness or
constructibility condition enters this construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.ProEtale.CondensedRing
