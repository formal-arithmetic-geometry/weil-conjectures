/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceDerivedHom
public import WeilConjectures.AlgebraicGeometry.PointDerivedHom.PointPullbackDerivedHom
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluationData

/-! # Evaluation coherence for free profinite parameters

Source: Stacks Project, Tags 08J7, 08J9 and 07A7; the generator and scalar
adjunction calculations in the node
(blueprint: def-sfb-free-parameter-evaluation-data).

All Hom objects are the recorded closed derived Hom. Gamma is the recorded
ProfiniteFreeSlice.Comparison.gamma. The maps below precede all coherence claims.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
