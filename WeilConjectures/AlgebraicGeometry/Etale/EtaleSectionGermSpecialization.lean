/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleStalkSpecialization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricSpecializationStrictLocalLift

/-! # Specialization invariance of the bijectivity locus of a section map

Source: Stacks Project, Tags 0GJ2, 0GJ5, 0GJ6 and 0GKC.
(blueprint: lem-weil-pbc-etale-section-germ-specialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

end AlgebraicGeometry.Scheme
