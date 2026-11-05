/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts

/-!
# Morphisms out of a retract of a coproduct in the derived category

Let `C` be an abelian category with K-injective resolutions. Suppose that a cochain complex `M` is
a retract of a coproduct `P = ∐ᵢ Nᵢ` of complexes, via `s : M ⟶ P` and `t : P ⟶ M` with
`s ≫ t = 𝟙 M`. A morphism `δ : Q(M) ⟶ Y` in the derived category which vanishes on each of the
components `Q(ιᵢ ≫ t) : Q(Nᵢ) ⟶ Q(M)` is zero
(`DerivedCategory.eq_zero_of_Q_map_inj_comp_comp_eq_zero`, and its variant for two morphisms
`DerivedCategory.eq_of_Q_map_inj_comp_comp_eq`): indeed `Q` sends coproducts of
complexes to coproducts (`DerivedCategory.isColimitCofanMkQObj`), so `Q(t) ≫ δ` vanishes, and
`δ = Q(s) ≫ Q(t) ≫ δ`.

This allows one to deduce the vanishing of `δ` from a *locally finite* decomposition of the
identity of `M`, whose components need not form a finite sum.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]

end DerivedCategory
