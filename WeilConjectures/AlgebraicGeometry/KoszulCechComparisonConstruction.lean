/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedDifferential

/-! # The canonical Koszul-to-Čech comparison

Source: Stacks Project, Tags 08CX, 08D0 and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
The power system, its colimit, and its comparison map retain the explicit basis formula
and the totalization sign of Tag 08D1. Existence proofs supply only verification data.
-/

@[expose] public section

universe uK wK vK

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)

variable (M : CochainComplex (ModuleCat.{uK} A) ℤ)

variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

variable [HasDerivedCategory.{wK}
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace))]
  [HasDerivedCategory.{vK} (ModuleCat.{uK} A)]

end
end AlgebraicGeometry
