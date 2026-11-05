/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.LocalizationCech.ExtendedLocalizationCechSupplement
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-! # Signed contraction of the sheaf Koszul complex

Source: Stacks Project, Tags 0626, 0663, 0913 and 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.LocalizationCech

section Generic
variable {D : Type*} [Category D] [Abelian D]
end Generic

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

end SheafOfModules.LocalizationCech
