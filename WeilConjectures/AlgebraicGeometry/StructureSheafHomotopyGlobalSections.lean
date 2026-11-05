/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Single

/-! # Evaluation at one on homotopy classes of structure-sheaf maps

Source: Stacks Project, Tag 09M1, proof, first paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- Lift chain maps and homotopies componentwise using the same inverse on each Hom set.

-- A map out of the unit is determined by one on the total open; restrict it to each open.

-- Transport the degree-zero bijection along the single-complex component isomorphism.

end AlgebraicGeometry
