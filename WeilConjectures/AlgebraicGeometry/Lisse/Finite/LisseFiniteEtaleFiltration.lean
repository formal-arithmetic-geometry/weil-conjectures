/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Coinvariants
import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorModuleDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorModuleComparisons
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PrimaryPGroupFiltration

/-!
# Prime-to-primary finite étale filtration covers

Source: Stacks Project, Tags 0GJ0 and 0DV5 (3), with componentwise assembly on an
affine Noetherian base (blueprint: lem-weil-pbc-etale-lisse-finite-etale-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
