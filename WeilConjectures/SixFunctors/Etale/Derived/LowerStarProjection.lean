/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!
# The projection map for the derived pushforward

Let `p : X ⟶ Y` be a morphism of schemes. We construct the projection map
`Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)`, natural in `M` in `D(X_ét)` and `L` in `D(Y_ét)`.
It is the transpose along the adjunction `Lp^* ⊣ Rp_*` of the composite
```
 Lp^*(Rp_*M ⊗ᴸ L) ⟶ Lp^*Rp_*M ⊗ᴸ Lp^*L ⟶ M ⊗ᴸ Lp^*L
```
of the comparison `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison` and the
counit of the adjunction tensored with the identity of `Lp^*L`.

## Main definitions and results

- `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap p`: the projection map, as a
  natural transformation of bifunctors `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`.
- `AlgebraicGeometry.Etale.homEquiv_symm_rightDerivedLowerStarProjectionMap`: its adjoint is
  the composite above.

The results depend on `sorryAx` through `AlgebraicGeometry.Etale.derivedTensor`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The morphism `Lp^*(Rp_*M ⊗ᴸ L) ⟶ M ⊗ᴸ Lp^*L` in `D(X_ét)`, composite of the comparison
`Lp^*(Rp_*M ⊗ᴸ L) ⟶ Lp^*Rp_*M ⊗ᴸ Lp^*L` and of the counit of `Lp^* ⊣ Rp_*` tensored with
the identity of `Lp^*L`. It is the adjoint of the projection map
`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`. -/
noncomputable def rightDerivedLowerStarProjectionMapAdj
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((p)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj (R((p)_*[A]).obj M)).obj L) ⟶
      ((-⊗ᴸ-(X)[A]).obj M).obj (L((p)^*[A]).obj L) :=
  ((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)).app L ≫
    ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)).app
      (L((p)^*[A]).obj L)

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` for the derived pushforward along
`p : X ⟶ Y`, as a natural transformation of bifunctors `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`.
It is the transpose along `Lp^* ⊣ Rp_*` of
`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMapAdj`. -/
noncomputable def rightDerivedLowerStarProjectionMap :
    R((p)_*[A]) ⋙ -⊗ᴸ-(Y)[A] ⟶
      (Functor.postcompose₂.obj R((p)_*[A])).obj
        ((Functor.whiskeringLeft₂ _).obj (𝟭 _) |>.obj L((p)^*[A]) |>.obj (-⊗ᴸ-(X)[A])) where
  app M :=
    { app L := (derivedUpperStarLowerStarAdjunction A p).homEquiv _ _
        (rightDerivedLowerStarProjectionMapAdj A p M L)
      naturality L L' f := by
        dsimp
        rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
        congr 1
        simp only [rightDerivedLowerStarProjectionMapAdj, Category.assoc]
        have h := ((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)).naturality f
        dsimp at h
        rw [reassoc_of% h]
        exact congrArg _ ((((-⊗ᴸ-(X)[A]).map
          ((derivedUpperStarLowerStarAdjunction A p).counit.app M))).naturality _) }
  naturality M M' f := by
    refine NatTrans.ext (funext fun L ↦ ?_)
    dsimp
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
    congr 1
    have h := NatTrans.congr_app
      ((leftDerivedUpperStarTensorComparison A p).naturality (R((p)_*[A]).map f)) L
    dsimp at h
    simp only [rightDerivedLowerStarProjectionMapAdj, reassoc_of% h, Category.assoc,
      ← NatTrans.comp_app, ← Functor.map_comp]
    exact congrArg (fun g ↦ _ ≫ ((-⊗ᴸ-(X)[A]).map g).app _)
      ((derivedUpperStarLowerStarAdjunction A p).counit_naturality f)

@[simp]
lemma rightDerivedLowerStarProjectionMap_app_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((rightDerivedLowerStarProjectionMap A p).app M).app L =
      (derivedUpperStarLowerStarAdjunction A p).homEquiv _ _
        (rightDerivedLowerStarProjectionMapAdj A p M L) :=
  rfl

/-- The adjoint of the projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` along
`Lp^* ⊣ Rp_*` is the composite
`Lp^*(Rp_*M ⊗ᴸ L) ⟶ Lp^*Rp_*M ⊗ᴸ Lp^*L ⟶ M ⊗ᴸ Lp^*L` of the comparison and the counit. -/
lemma homEquiv_symm_rightDerivedLowerStarProjectionMap
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedUpperStarLowerStarAdjunction A p).homEquiv _ _).symm
        (((rightDerivedLowerStarProjectionMap A p).app M).app L) =
      ((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)).app L ≫
        ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)).app
          (L((p)^*[A]).obj L) := by
  simp [rightDerivedLowerStarProjectionMapAdj]

end Etale

end AlgebraicGeometry
