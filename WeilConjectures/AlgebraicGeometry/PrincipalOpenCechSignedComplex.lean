/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # PrincipalOpenCechSignedComplex

Source: Stacks Project, Cohomology, Tag 08C1.
(blueprint: lem-sc-principal-open-cech-signed-complex).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

namespace CoordinateConstruction
noncomputable section

variable (A : Type u) [CommRing A]

variable {A} (r : ℕ) (f : Fin r → A)

variable (F : CochainComplex
  (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

end
end CoordinateConstruction

end AlgebraicGeometry
