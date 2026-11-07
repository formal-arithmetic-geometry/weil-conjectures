/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Submission.WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.QuasiSeparated
import Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohPerfectGeneration
import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplexRepresentatives
import Submission.WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import Submission.WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import Submission.WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator
import Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGenerationCore

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Compact generation of the quasi-coherent derived category

Source: Stacks Project, Derived Categories of Schemes, Theorem 36.15.3 (Tag 09IS),
and Derived Categories, Definition 13.37.5 (Tag 09SQ)
(blueprint: lem-pc-derived-qcoh-compact-generation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
