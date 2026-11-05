/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-! # Closed support over the intrinsic constant coefficient sheaf

Source: Weil blueprint, smooth purity, order 1858; Stacks Project, Tag 09AH
(blueprint: def-exc-proetale-sections-with-support).

The canonical coefficient map, obtained by applying inverse image to constant sections,
identifies the pulled-back constant ring with the constant ring on the source. All module
operations below use that map. No replacement of the small pro-etale site is made.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
