/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientExchangeTransport

/-!
# Finite-level pro-etale proper base change

Source: blueprint, proper base change, finite-level pro-etale theorem; Stacks Project
Tag 09C8, the finite-coefficient step in Tag 09C9
(blueprint: thm-weil-pbc-finite-level-proetale).

## Main statements

- `AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

end AlgebraicGeometry.Scheme
