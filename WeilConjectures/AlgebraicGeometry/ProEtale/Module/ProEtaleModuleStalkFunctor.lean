/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Functorial module stalks on the pro-etale site

Source: Stacks Project, Tags 0F6B and 002F
(blueprint: def-weil-proetale-geometric-stalk).
The objects and scalar action are the recorded module colimit construction;
this interface retains the induced maps and additivity needed for complexes.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

attribute [instance] geometricRingModuleStalkFunctor_additive

end AlgebraicGeometry.Scheme
