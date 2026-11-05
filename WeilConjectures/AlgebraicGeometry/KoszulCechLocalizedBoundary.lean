/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedEvaluation
import WeilConjectures.AlgebraicGeometry.KoszulCechBoundaryEvaluation
import Mathlib.Data.Nat.Choose.Basic

/-! # The horizontal localized Koszul boundary calculation

Source: Stacks Project, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-localized-boundary).
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

end AlgebraicGeometry
