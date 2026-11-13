/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Algebra.Category.Grp.AB

meta import Mathlib.Lean.Meta.CongrTheorems

/-!
# Module and derived comparison for pullback from the condensed point

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
pp. 5--6, pullback paragraph before (3.1), Remark 3.2 and Definition 3.5.

The ordinary comparison is the existing `CondensedRing.upperStarFromPointModComp`.
Its scalar cancellation uses the specified coefficient isomorphism, and its underlying
map is `upperStarFromPointComp`. The internal module categories are identified with
sectionwise module sheaves by `InternalAbelianSheafModule.sectionModuleEquivalence`;
`InternalModuleOperations.upperComparison` identifies the two module inverse images.
All derived categories here are ordinary and unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory

/-- Point-module inverse image preserves finite limits.
Source: HRS Section 3, pp. 5--6. -/
@[instance]
theorem condensedPointModule_preservesFiniteLimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (CondensedRing.upperStarFromPointMod Λ X) := by
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  unfold CondensedRing.upperStarFromPointMod
  infer_instance

/-- Point-module inverse image preserves finite colimits.
Source: HRS Section 3, pp. 5--6. -/
@[instance]
theorem condensedPointModule_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (CondensedRing.upperStarFromPointMod Λ X) := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits
  unfold CondensedRing.upperStarFromPointMod
  infer_instance

/-- Point-module inverse image is additive.
Source: HRS Section 3, pp. 5--6. -/
@[instance]
theorem condensedPointModule_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (CondensedRing.upperStarFromPointMod Λ X).Additive := by
  have : PreservesBinaryBiproducts (CondensedRing.upperStarFromPointMod Λ X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end AlgebraicGeometry.ProEtale
