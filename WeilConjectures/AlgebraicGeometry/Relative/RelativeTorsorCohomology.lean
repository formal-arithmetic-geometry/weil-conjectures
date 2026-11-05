/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorClassNaturality
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorForgetNormalization
import Mathlib.CategoryTheory.Preadditive.Comma
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions

/-!
# Relative first cohomology and torsors with an open section

Source: Stacks Project, Cohomology on Sites, Tag 03AJ, relative refinement in the
DAG proof; compare Cohomology Tags 0G71 and 0G78
(blueprint: lem-amb-relative-torsor-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
