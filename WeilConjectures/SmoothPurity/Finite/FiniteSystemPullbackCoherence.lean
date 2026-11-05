/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleComparisonLocalization

/-! # Coherent composition of finite-coefficient pullback on strict systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, and sites-modules.tex,
Tags 03D3, 03D7, 03D8. The strict-system refinement uses componentwise adjunctions
and coherence before localization
(blueprint: lem-pod-finite-system-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Replaying sectionwise transport proofs for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures.SemilinearSections

namespace WeilConjectures

-- DS fixes this localization; use it also when inferring exact derived functors.
attribute [local instance 3000] SemilinearSections.hasDerived

variable (A : ℕ → CommRingCat.{u}) (τ : ∀ n, A (n + 1) ⟶ A n)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.leftAdjoint proEtaleRingModulePullback
  proEtaleRingDirectImageMap proEtaleRingModuleAdjunction
  AlgebraicGeometry.ProEtale.VaryingRing.ringMap
  AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP
  AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj

attribute [local irreducible] WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.rings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] finiteSystemComposition finiteSystemPullbackEvaluation
  finiteSystemDerivedComposition finiteSystemDerivedPullbackEvaluation
  finiteSystemModuleComposition finiteSystemComplexComposition

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.modulePComp

@[irreducible] private def systemDirectComposition (A : ℕ → CommRingCat.{u})
    (τ : ∀ n, A (n + 1) ⟶ A n) {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemPushforward.{u} A τ h ⋙ finiteSystemPushforward.{u} A τ k ≅
      finiteSystemPushforward.{u} A τ (h ≫ k) :=
  AlgebraicGeometry.ProEtale.VaryingRing.modulePComp
    (systemCoefficientRings.{u} A) (systemCoefficientMaps.{u} A τ) h k

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section CanonicalLevelStructures

-- Fix the same level structures as the canonical finite-coefficient derived operations.

end CanonicalLevelStructures

end WeilConjectures
