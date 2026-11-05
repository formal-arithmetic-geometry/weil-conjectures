/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart

/-! # Quasi-coherence and support of derived internal Hom

Source: Stacks Project, Derived Categories of Schemes, Tag 0A6H (1), (2),
and the support observation in the proof of Tag 0A9C
(blueprint: lem-sc-rhom-supported-qcoherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
