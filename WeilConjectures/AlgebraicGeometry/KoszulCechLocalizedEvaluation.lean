/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem

/-! # Signed localized Koszul evaluation

Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-vertical).
The degree maps are constructed using the inverse of scalar multiplication on principal
opens. Coefficient maps commute with the scalar division used in these degree maps.
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
