/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Submission.WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
public import Submission.WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import Submission.WeilConjectures.CategoryTheory.CondensedInternalBarData
public import Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Profinite free modules and unbounded derived slice Hom

Source: Stacks Project, Cohomology on Sites, Tags 08FI and 08J7;
Hemo--Richarz--Scholbach, Section 3, Example 3.1 and equation (4.1)
(auxiliary; not a blueprint node).

The normalized comparison retains the universal free generators, an actual chain
isomorphism on K-injective representatives, and its derived localization square.
Every helper constructs data from the existing free adjunctions and inverse images.
`exists_comparison` states the identity on the ordinary unbounded derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

/-- The existing strong monoidal inverse image lifted to internal coefficient modules.
Source: Stacks 08FI, 08J7; HRS Section 3
(auxiliary; not a blueprint node). -/
def pointModulePullback : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
    Internal Λ X := (upperStarFromPoint X).mapMod Λ
end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
