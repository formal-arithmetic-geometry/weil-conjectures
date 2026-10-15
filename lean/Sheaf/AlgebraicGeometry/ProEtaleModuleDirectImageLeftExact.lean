/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Left exactness of pro-etale module direct image

Source: Stacks Project, Tags 03DA and 03DC, and the Weil conjectures blueprint,
`def-weil-derived-direct-image`, first paragraph
(blueprint: lem-weil-proetale-module-direct-image-left-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Direct image of constant-ring module sheaves on the small pro-etale sites is
additive and left exact. In these abelian categories, preservation of finite limits
is equivalent to preserving exact sequences `0 → F' → F → F''`.

Source: Stacks Project, Tags 03DA and 03DC; blueprint `def-weil-derived-direct-image`,
first paragraph (blueprint: lem-weil-proetale-module-direct-image-left-exact).

Proof plan: addition of morphisms is sectionwise. Precomposition with base change
therefore preserves sums and zero morphisms. Kernels are computed sectionwise:
at `V` the direct image of the kernel is the kernel over `V ×[Y] X`. Its scalar action
is restriction along the same canonical constant-ring map on both sides, so these
identifications are linear and compatible with restrictions. The zero sheaf is also
preserved. An exact sequence beginning with zero identifies its first term with the
kernel of its second arrow; the functor preserves this identification and hence the
sequence. Equivalently, additivity preserves finite biproducts, and preservation of
kernels and the zero object then gives preservation of all finite limits. -/
theorem proEtaleConstantModuleDirectImage_additive_leftExact
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] :
    (proEtaleConstantModuleDirectImage f A).Additive ∧
      PreservesFiniteLimits (proEtaleConstantModuleDirectImage f A) := by
  sorry

end AlgebraicGeometry.Scheme
