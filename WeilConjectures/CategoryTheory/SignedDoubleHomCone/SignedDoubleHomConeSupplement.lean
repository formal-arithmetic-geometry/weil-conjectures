/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import WeilConjectures.Algebra.Homology.SignedDoubleHomCone

/-!
# Signed double internal Hom and mapping cones

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08JC;
derived.tex, Definition 014E (blueprint: lem-sf-double-hom-cone-comparison).
The component equations below are equations of module sheaves, hence include every
local section and all restriction maps. Mathlib orders the cone summands as A[1], B.
-/

@[expose] public section

set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.homComplexFunctor

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SignedDoubleHomCone

namespace Calculation

-- Work through the projection API in an arbitrary preadditive category.
-- This keeps the component calculations independent of the sheaf implementation.

universe u' v'
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]

variable {F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ}

-- Step 3: the two unsigned summands of Hom(Cone(f), I).

-- Steps 4 and 5: apply Hom again and insert the cone comparison sign.

-- Step 6: functoriality under commutative squares.

-- Steps 2 and 7: the composite shift comparison and the triangle arrows.

end Calculation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

end CategoryTheory.SignedDoubleHomCone
