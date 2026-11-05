/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax

/-! # Ordinary tensor comparison for completed coefficient transport

Source: Stacks Project, Modules on Sites, Tags 03DA and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v c' v' w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
