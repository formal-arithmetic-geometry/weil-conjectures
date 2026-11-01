/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionEvaluation
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.OpenIso
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.OpenNormalized
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.OpenEvaluation
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.ProperEvaluation

/-! # Finite normalization of system coefficient restriction

Source: the coefficient-composition argument, step 7; Stacks 03DI, 070Y and 0D6E;
Zheng Construction 4.1 (blueprint: lem-sp-system-restriction-finite-normalization).

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
