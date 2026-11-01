/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionEvaluation
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarRestrictionCocycle
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemOpenRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemProperRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemRestrictionFiniteNormalization

/-! # Restriction cocycle for compact support on strict coefficient systems

Source: the coefficient-composition detail of compact-support finite-field independence;
Stacks 03CZ, 03DI, 03DJ, 070Y and 0D6E; Zheng Construction 4.1
(blueprint: lem-weil-system-compact-support-restriction-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

variable {l : ℕ}

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
