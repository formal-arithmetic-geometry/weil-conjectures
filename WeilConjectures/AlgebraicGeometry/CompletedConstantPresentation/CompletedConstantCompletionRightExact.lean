/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedConstantPresentation.CompletedConstantCompletionFunctor
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Maps

/-! # Right exactness of completed constant finite modules

Source: Stacks Project, More on Algebra, Tag 0912; Modules on Sites, Tags 093J--093M.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CompletedConstantPresentation

attribute [local instance] sections_preservesFiniteLimits

attribute [local instance] sections_preservesFiniteColimits

-- Correct each successive lift by the image of one fixed kernel module. This avoids
-- needing a separate surjectivity theorem for transitions between quotient kernels.

-- Artin-Rees over the completed ring controls the filtration after restriction to A.
-- Source: Stacks, Algebra, lemmas Artin-Rees (00IN) and map-AR.

-- Package the quotient maps as a functor before proving compatibility. Induction can
-- then use the functor laws without unfolding quotient constructions in its motive.

-- Shift arbitrary lifts by the uniform Artin-Rees bound. Their differences then vanish
-- in the required quotients, so the shifted lifts define a section of the limit.

end AlgebraicGeometry.Scheme.CompletedConstantPresentation
