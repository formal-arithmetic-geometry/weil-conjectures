/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechHomologySurjective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechHomologyInjective

/-! # Alternating total Čech complexes on finite principal covers

Source: Stacks Project, Cohomology, Sections 20.25 and 20.40, and Tag 08D2
(blueprint: def-sc-principal-open-alternating-total).
Nonempty subsets index the alternating rows; the empty cover gives the zero complex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC wC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

variable (A : Type uC) [CommRing A]

variable {A} (r : ℕ) (f : Fin r → A)

variable (F : CochainComplex
  (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

variable [HasDerivedCategory.{wC}
  (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace))]
  [HasDerivedCategory.{vC} (ModuleCat.{uC} A)]

end
end AlgebraicGeometry
