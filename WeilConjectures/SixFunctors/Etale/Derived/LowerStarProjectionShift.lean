/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift

/-!
# The projection map of `Rp_*` in its second variable

For `p : X ⟶ Y` and a fixed `M` in `D(X_ét)`, the projection map
`Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`)
is a natural transformation between triangulated functors of `L` which commutes with the shifts
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_app_commShift`), and it is an
isomorphism at the unit `L = Λ_Y`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit`).
So the objects `L` at which it is an isomorphism are closed under cones.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The derived pullback `Lg^*` is triangulated, being isomorphic to the functor `D(g^*)`
induced by the exact pullback. -/
instance isTriangulated_leftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).IsTriangulated :=
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility _ ℤ
  Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

variable [Etale.UpperStarPreservesFlat A] {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` of the derived pushforward commutes
with the shifts in `L`. -/
lemma rightDerivedLowerStarProjectionMap_app_commShift
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (-⊗ᴸ-(Y)[A]).obj (R((p)_*[A]).obj M))
      (F₂ := (L((p)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj M) ⋙ R((p)_*[A]))
      ((rightDerivedLowerStarProjectionMap A p).app M) ℤ :=
  have : NatTrans.CommShift
      ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor (DerivedCategory
      (Sheaf X.smallEtaleTopology A))).map
        ((derivedUpperStarLowerStarAdjunction A p).counit.app M)) ℤ)
  Adjunction.commShift_rightAdjointProjectionMap_app (derivedUpperStarLowerStarAdjunction A p)
    (leftDerivedUpperStarTensorComparison A p) M

/-- The projection map `Rp_*M ⊗ᴸ 𝟙 ⟶ Rp_*(M ⊗ᴸ Lp^*𝟙)` at the unit is an isomorphism. -/
lemma isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A p).app M).app (𝟙_ _)) :=
  letI := leftDerivedUpperStarOplaxMonoidal A p
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η A p
  Adjunction.isIso_rightAdjointProjectionMap_app_app_tensorUnit
    (derivedUpperStarLowerStarAdjunction A p) (leftDerivedUpperStarTensorComparison A p)
    (fun _ _ ↦ rfl) M

end Etale

end AlgebraicGeometry
