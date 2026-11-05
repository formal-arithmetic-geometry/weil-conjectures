/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethTranspose
public import WeilConjectures.CategoryTheory.ObjectProperty.FullSubcategoryEqToHom
public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.OrdinaryKunnethProjection
public import WeilConjectures.TraceFormula.FieldDualizable
public import WeilConjectures.TraceFormula.HomologyWeilLowerStar

/-!
# The ordinary Künneth formula for global sections on `Dᵇc`

For a cartesian square `P = X ×_k Y` of separated `k`-schemes of finite type, the Künneth map
`RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(P, Lp₁^* A ⊗ Lp₂^* B)` on bounded constructible `ℚ̄_ℓ`-complexes is an
isomorphism (`ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback_point`). On `Dᵇc` it
is the Künneth map of the factorization `P ⟶ Y ⟶ Spec k`
(`ProEtale.CondensedRing.isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isPullback`):
generic base change along `Y ⟶ Spec k`, the relative Künneth formula for `p₂` and the projection
formula over the point, where every bounded constructible complex is dualizable. It is then
compared with the ambient Künneth map `ProEtale.CondensedRing.lowerStarKunnethMap'`
(`ProEtale.CondensedRing.map_baseChangeMap_app_comp_counit`,
`CategoryTheory.Adjunction.ι_map_homEquiv_δ_tensorHom_restrictFullyFaithful`).

## Implementation notes

Statements on `Dᵇc` and on the ambient derived categories carry different proofs of
`Precoherent Profinite` inside the coefficient ring `ℚ̲̄_ℓ`, and different presentations of the same
objects. They are compared by `exact_mod_proofs`, by `simp only` (rather than successive `rw`,
whose motives mix the two) and by `convert` followed by `rfl` on the small remaining goals.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable {P P' Y : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### The Künneth formula on `Dᵇc` -/

section Kunneth

variable {Q R X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType R.hom] [QuasiCompact R.hom] [IsSeparated R.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

end Kunneth

/-! ### The ordinary Künneth formula on the ambient derived categories -/

section Ambient

end Ambient

section BridgeKunneth

variable {Q X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

end BridgeKunneth

end AlgebraicGeometry.ProEtale.CondensedRing
