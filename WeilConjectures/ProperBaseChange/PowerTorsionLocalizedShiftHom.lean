/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Derived orthogonality of power-torsion cohomology and localized coefficients -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private noncomputable local instance pointEval_isEquivalence (A : CommRingCat.{u}) :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private noncomputable local instance pointConstant_isEquivalence (A : CommRingCat.{u}) :
    (pointConstant A).IsEquivalence := (pointEquivalence A).isEquivalence_inverse

private local instance pointConstant_additive (A : CommRingCat.{u}) :
    (pointConstant A).Additive where
  map_add := by intros; rfl

private local instance pointEval_additive (A : CommRingCat.{u}) :
    (pointEval A).Additive where
  map_add := by intros; rfl

end AlgebraicGeometry
