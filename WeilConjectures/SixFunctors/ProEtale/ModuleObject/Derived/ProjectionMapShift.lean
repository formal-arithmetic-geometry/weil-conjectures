/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!
# The projection map of module objects commutes with the shifts

Let `Λ` be a commutative condensed ring and `p : X ⟶ Y` a morphism of schemes. The projection
map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` of module objects over `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.projectionMap`) commutes with the shifts in each
variable, as does the tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`) out of which it is built.
This is the compatibility of the projection map with the triangulated structure ("the projection
map is compatible with shifts and cones") used when extending the projection formula from
`Dbc` to `Loc(Dbc)`.

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.commShift_projectionMap_app`: the projection map
  commutes with the shifts in `L`.
- `AlgebraicGeometry.ProEtale.CondensedRing.commShift_projectionMap_flipApp`: the projection map
  commutes with the shifts in `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L` commutes with the shifts in `L`. -/
instance commShift_leftDerivedUpperStarTensor_app (K : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).obj K ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj (L((p)^*⟦Λ⟧).obj K))
      ((leftDerivedUpperStarTensor Λ p).app K) ℤ :=
  sorry

/-- The tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L` commutes with the shifts in `K`. -/
instance commShift_leftDerivedUpperStarTensor_flipApp (L : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).flip.obj L ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj L))
      (NatTrans.flipApp (leftDerivedUpperStarTensor Λ p) L) ℤ :=
  sorry

/-- The image of a morphism under the derived tensor product commutes with the shifts in the
second variable. -/
instance commShift_curriedTensor_map {Z : Scheme.{u}} {K K' : 𝔻(Z)} (φ : K ⟶ K') :
    NatTrans.CommShift ((curriedTensor 𝔻(Z)).map φ) ℤ :=
  inferInstance

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` commutes with the shifts in `L`. -/
instance commShift_projectionMap_app (M : 𝔻(X)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).obj (R((p)_*⟦Λ⟧).obj M))
      (F₂ := (L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj M) ⋙ R((p)_*⟦Λ⟧))
      ((projectionMap Λ p).app M) ℤ :=
  Adjunction.commShift_rightAdjointProjectionMap_app (derivedUpperStarLowerStarAdjunction Λ p)
    (leftDerivedUpperStarTensor Λ p) M

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` commutes with the shifts in `M`. -/
instance commShift_projectionMap_flipApp (L : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := R((p)_*⟦Λ⟧) ⋙ (curriedTensor 𝔻(Y)).flip.obj L)
      (F₂ := (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj L) ⋙ R((p)_*⟦Λ⟧))
      (NatTrans.flipApp (projectionMap Λ p) L) ℤ :=
  Adjunction.commShift_rightAdjointProjectionMapFlipApp (derivedUpperStarLowerStarAdjunction Λ p)
    (leftDerivedUpperStarTensor Λ p) L ℤ

end AlgebraicGeometry.ProEtale.CondensedRing
