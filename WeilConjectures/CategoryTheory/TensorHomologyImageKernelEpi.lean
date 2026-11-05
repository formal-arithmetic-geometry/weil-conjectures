/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor homology maps onto the kernel of the image inclusion

Source: Stacks Project, Tag 0653, the Tor argument in `lemma-last-one-flat`.
(blueprint: lem-pc-module-tensor-homology-image-kernel-epi).
-/

@[expose] public section

universe u

namespace CategoryTheory

open MonoidalCategory Limits

end CategoryTheory
