/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedEvaluation
import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedBoundary

/-! # The differential identity for signed localized Koszul evaluation

Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The degree maps are constructed using the inverse of scalar multiplication on principal
opens. Only their compatibility with adjacent differentials remains to be proved.
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A]
variable (S : SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) (s : A)

variable (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

end AlgebraicGeometry
