/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Detecting cohomology vanishing on a finite standard-open cover

Source: Stacks Project, Tag 066D, proof, first paragraph, and Tag 00EO (1).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

attribute [local instance 2000] CommRing.toRing

open TensorProduct

end DerivedCategory
