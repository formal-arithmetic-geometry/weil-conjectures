/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionData

/-! # Finite evaluation of normalized compact-support restriction

Source: Stacks 03DI and 0D6E; Zheng Construction 4.1; the coefficient-composition detail
(blueprint: def-sp-system-compact-support-restriction-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

variable {l : ℕ}

/-- The actual coefficient map at a finite level.
Source: Zheng 4.1 (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
abbrev levelMap (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (ProEt.topology W) CommRingCat.{u + 1}).map (a.app (op n))

/-- Finite-level exact restriction, using the existing module-sheaf restriction.
Source: Stacks 03CZ (blueprint: def-sp-system-compact-support-restriction-evaluation). -/
abbrev levelRestriction (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :=
  (res.{u + 1, u, u + 1} (levelMap W a n)).mapDerivedCategory

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
