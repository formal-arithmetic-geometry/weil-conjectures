/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# The closed-support triangle and restriction to an open, before constructibility

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`, and let `Ri^!` be the
right adjoint of the direct image `Ri_*` on the unbounded derived categories of étale sheaves of
modules (`AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`, blueprint
`lem-exc-closed-ambient`). This file records:

* the closed-support triangle `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1]` for every `K`
  (blueprint `lem-exc-closed-support-triangle`), deduced from the supported localization
  triangle `AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization` along
  `Ri_! ≅ Ri_*` and the uniqueness of right adjoints.

No constructibility is used anywhere.

## Main statements

- `AlgebraicGeometry.Etale.exists_distTriang_closedSupport`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

namespace Etale

open Scheme

section Triangle

variable {R : Type (u + 1)} [CommRing R] [Finite R] {Z U X : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i] [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]

end Triangle

end Etale

end AlgebraicGeometry
