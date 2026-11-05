/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Perfect complexes on schemes

Source: literature/blueprint/master/blueprint/sec-picard-framework/det-thm-picard-semicon/
def-pc-perfect-complex.md, node def-pc-perfect-complex, order 664; Stacks Project,
Cohomology of Sheaves, Definitions 08C4 and 08CM, Tag 0BDH (blueprint: def-pc-perfect-complex).

Restriction to an open is `SheafOfModules.overFunctor` on the localized site, with the same
module category and derived category as `schemeDerivedCategory`, in the shape of
`AlgebraicGeometry.Scheme.IsPseudoCoherent` (blueprint: def-pur-pseudo-coherent-complex).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
