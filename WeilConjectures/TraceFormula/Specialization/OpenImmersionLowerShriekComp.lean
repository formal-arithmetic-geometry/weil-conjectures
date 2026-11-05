/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Identity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
public import WeilConjectures.Tactic.ExactModProofs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-!

# The composition isomorphism of the lower shriek for open immersions

For open immersions `j : Y ⟶ X` and `ι : X ⟶ Z` of separated `k`-schemes of finite type, the
composition isomorphism `R(j ≫ ι)_! ≅ Rj_! ⋙ Rι_!` of the lower shriek on bounded constructible
`ℚ̄_ℓ`-complexes is, through the identifications `Rf_! ≅ f_!` of the lower shriek of an open
immersion with the extension by zero, the composition isomorphism `(j ≫ ι)_! ≅ j_! ⋙ ι_!` of the
extensions by zero
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion`
).

The composition isomorphism of the lower shriek is computed by any triangle of compactifications
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`); for the
triangle of the trivial compactifications `Y ⟶[j] X ⟶[𝟙] X`, `X ⟶[ι] Z ⟶[𝟙] Z` and
`Y ⟶[j ≫ ι] Z ⟶[𝟙] Z`, the composition isomorphism of the triangle in the exchange formalism is
the composition isomorphism of the extensions by zero, read through `R(𝟙)_* ≅ 𝟭`
(`CategoryTheory.ExchangeFormalism.compIso_ofComp_hom_app`).

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.ExchangeFormalism

universe w v₁ v u

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

end CategoryTheory.ExchangeFormalism

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

variable {Y X Z : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
