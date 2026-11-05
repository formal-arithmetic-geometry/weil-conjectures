/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

/-!
# Derived pro-etale direct image and restriction of scalars

Source: blueprint `def-weil-derived-direct-image`, order 1468, coefficient tower maps;
Stacks Project, Tags 0D6E, 0D6J and 015F
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
-/

@[expose] public section

set_option autoImplicit false

universe u uC uD vC vD wC wD

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Generalize the structure maps before substituting their adjunction equalities.
-- This keeps sectionwise morphism coercions dependent on the maps throughout transport.

end AlgebraicGeometry.Scheme
