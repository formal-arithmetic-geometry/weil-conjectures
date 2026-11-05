/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

/-! # Canonical pullback comparison on global derived Hom
Source: Stacks Project, Cohomology, Remark 08I3 and Section 0B6A;
Duality, Tag 0AA8 (blueprint: def-pc-global-hom-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe uP wP
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{uP},
  HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type uP) [Ring R], HasDerivedCategory.{wP} (ModuleCat.{uP} R)]

end AlgebraicGeometry
