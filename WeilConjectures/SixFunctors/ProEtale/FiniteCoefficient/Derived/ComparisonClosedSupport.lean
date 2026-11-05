/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# The closed-support triangle pulled back to the pro-étale site

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` a complementary quasi-compact open
immersion. For a bounded below object `M` of `D(X_ét, Λ)`, the étale closed-support triangle
`Ri_* Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶` is sent by the comparison pullback `ν_X^*` to a distinguished
triangle of `D(X_proét, Λ)`, whose outer vertices are identified with
`Ri_* ν_Z^* (Ri^! M)` and `Rj_* ν_U^* (j^* M)` by the comparison of direct images on bounded
below objects (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso`).

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.exists_distTriang_mapDerivedCategory_closedSupport`:
  there are bounded below `C ∈ D(Z_ét, Λ)`, `N ∈ D(U_ét, Λ)` and a distinguished triangle
  `Ri_* ν_Z^* C ⟶ ν_X^* M ⟶ Rj_* ν_U^* N ⟶ (Ri_* ν_Z^* C)⟦1⟧` in `D(X_proét, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme _root_.DerivedCategory.TStructure

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}}

end AlgebraicGeometry.ProEtale.DerivedCategory
