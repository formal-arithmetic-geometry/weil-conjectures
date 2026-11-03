/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# Inverse limits for pulled-back condensed coefficients

Source: latest blueprint, part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sk-prop-open-coefficients/lem-sfb-dc-lower-star-preserves.md
(lem-sfb-dc-lower-star-preserves), integral-coefficient paragraph, and Stacks
Tags 079P and 070K (blueprint: def-pur-completed-rlim-functor).

The coefficient category is the recorded internal-module category over `p_X^* Λ`.
Index `n : ℕ` means the paper's positive level `n + 1`. The derived categories use
explicit localization universes, as required by the recorded size convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wT wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedInverseLimit

variable (X : Scheme.{u})
  (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))

/-- Strict inverse sequences of actual internal `p_X^* Λ`-modules; level `n` means `n+1`.
Source: latest blueprint, integral Rlim paragraph; def-weil-inverse-system
(blueprint: def-pur-completed-rlim-functor). -/
abbrev strictTowers : Type (u + 2) :=
  ℕᵒᵖ ⥤ condensedModuleCategory X Λ.toMon

variable [HasDerivedCategory.{wT} (strictTowers X Λ)]
  [HasDerivedCategory.{wA} (condensedModuleCategory X Λ.toMon)]

end AlgebraicGeometry.ProEtale.CondensedInverseLimit
