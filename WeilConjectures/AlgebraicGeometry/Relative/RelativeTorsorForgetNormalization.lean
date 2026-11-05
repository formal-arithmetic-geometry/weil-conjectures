/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.CategoryTheory.Abelian.FirstResolutionExtensionClass

/-!
# Ordinary normalization of framed relative classes

Source: Stacks Project, Tag 03AJ, relative refinement, step 6.
(blueprint: lem-amb-relative-torsor-forget-normalization).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale

-- Check the axioms of the completed construction.
