/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen

/-! # SupportPart of derived internal Hom

Source: Stacks Project, Tag 0A9C proof
(blueprint: lem-sc-rhom-supported-qcoherent-support-part).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open scoped ZeroObject

end AlgebraicGeometry
