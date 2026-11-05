/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Relative étale cohomology in an injective-resolution model

Source: Stacks Project, Cohomology on Sites, Tag 03AJ, relative refinement; compare
Cohomology, Tags 0G71 and 0G78 (blueprint: def-amb-relative-etale-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
