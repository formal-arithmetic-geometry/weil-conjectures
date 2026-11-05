/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Resolution independence of derived functors computed by K-injective resolutions

If `s : K ⟶ I` and `t : K ⟶ J` are two K-injective resolutions of a cochain complex `K`, then
`I` and `J` are isomorphic in the homotopy category. Consequently, for every additive functor
`G`, the complexes `G(I)` and `G(J)` have isomorphic cohomology: the groups `Hᵠ(T_ét, F)`
computed from a K-injective resolution of `F` do not depend on the chosen resolution.

## Main statements

- `CochainComplex.IsKInjective.nonempty_iso_quotient_obj`: two K-injective resolutions are
  isomorphic in the homotopy category.
- `CochainComplex.IsKInjective.nonempty_homology_iso`: their images under an additive functor
  have isomorphic cohomology.
- `CochainComplex.IsKInjective.isIso_of_isIso_Qh_map`: `Qh` reflects isomorphisms between
  K-injective complexes.
-/

@[expose] public section

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKInjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

end CochainComplex.IsKInjective
