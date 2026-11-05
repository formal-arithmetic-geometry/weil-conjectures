/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Derived pullback/direct-image adjunction for ringed spaces

Source: Stacks Project, Cohomology, Tag 079W, Lemma cohomology-lemma-adjoint,
with Tag 06YJ, Lemma cohomology-lemma-derived-base-change
(blueprint: lem-pc-ringed-spaces-derived-adjoint-general).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

end AlgebraicGeometry.RingedSpace
