/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Comp

/-!
# The pro-étale projection map of the derived pushforward commutes with base change

For a commutative square `g' ≫ f = f' ≫ g` of schemes, the projection map
`Rf_*K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^*L)` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap`)
on pro-étale derived categories commutes with the derived base change map
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` (`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) and the tensor
comparisons of the derived pullbacks. This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange`.

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso_hom_tensor`: the isomorphism
  `Lg^* Lf'^* ≅ Lf^* Lg'^*` of a commutative square commutes with the tensor comparisons.
- `AlgebraicGeometry.ProEtale.derivedUpperStar_map_derivedBaseChangeMap_app_counit`: the adjoint
  form of `Ex_*`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`: the
  projection map commutes with `Ex_*` (part of blueprint
  `lemma-weil-pbc-projection-formula-base-change-naturality`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

namespace ProEtale

/-- The transport isomorphism `La^* ≅ Lb^*` along an equality `a = b` commutes with the tensor
comparisons of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarCongr_hom_tensor {Z Y : Scheme.{u}} {a b : Z ⟶ Y} (h : a = b)
    (x y : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((leftDerivedUpperStarTensorComparison A a).app x).app y ≫
        ((leftDerivedUpperStarCongr A h).hom.app x ⊗ₘ (leftDerivedUpperStarCongr A h).hom.app y) =
      (leftDerivedUpperStarCongr A h).hom.app (x ⊗ y) ≫
        ((leftDerivedUpperStarTensorComparison A b).app x).app y := by
  subst h
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, id_tensorHom_id]
  erw [Category.comp_id, Category.id_comp]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square `g' ≫ f = f' ≫ g`
commutes with the tensor comparisons of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarSquareIso_hom_tensor (sq : CommSq g' f' f g)
    (a b : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((f')^*[A]).map (((leftDerivedUpperStarTensorComparison A g).app a).app b) ≫
        ((leftDerivedUpperStarTensorComparison A f').app _).app _ ≫
        ((leftDerivedUpperStarSquareIso A sq).hom.app a ⊗ₘ
          (leftDerivedUpperStarSquareIso A sq).hom.app b) =
      (leftDerivedUpperStarSquareIso A sq).hom.app (a ⊗ b) ≫
        L((g')^*[A]).map (((leftDerivedUpperStarTensorComparison A f).app a).app b) ≫
        ((leftDerivedUpperStarTensorComparison A g').app _).app _ := by
  have h₁ := leftDerivedUpperStarTensorComparison_comp A f' g a b
  have h₂ := leftDerivedUpperStarTensorComparison_comp A g' f a b
  have h₃ := leftDerivedUpperStarCongr_hom_tensor A sq.w.symm a b
  dsimp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  have h₁' : L((f')^*[A]).map (((leftDerivedUpperStarTensorComparison A g).app a).app b) ≫
      ((leftDerivedUpperStarTensorComparison A f').app _).app _ =
      (leftDerivedUpperStarComp A f' g).inv.app (a ⊗ b) ≫
        ((leftDerivedUpperStarTensorComparison A (f' ≫ g)).app a).app b ≫
        ((leftDerivedUpperStarComp A f' g).hom.app a ⊗ₘ
          (leftDerivedUpperStarComp A f' g).hom.app b) := by
    rw [h₁, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% h₁', tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app_assoc, ← tensorHom_comp_tensorHom, reassoc_of% h₃, h₂]
  simp only [Category.assoc]

/-- **The adjoint form of the derived base change map**: for `K` in `D(X_proét)`, the composite
`Lf'^* Lg^* Rf_* K ⟶ Lf'^* Rf'_* Lg'^* K ⟶ Lg'^* K` of `Lf'^*(Ex_*)` and the counit of
`Lf'^* ⊣ Rf'_*` is the square isomorphism followed by `Lg'^*` of the counit of `Lf^* ⊣ Rf_*`. -/
@[reassoc]
lemma derivedUpperStar_map_derivedBaseChangeMap_app_counit (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (L((f')^*[A])).map ((derivedBaseChangeMap A sq).app K) ≫
        (derivedUpperStarLowerStarAdjunction A f').counit.app ((L((g')^*[A])).obj K) =
      (leftDerivedUpperStarSquareIso A sq).hom.app ((R((f)_*[A])).obj K) ≫
        (L((g')^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).counit.app K) :=
  mateEquiv_counit _ _ _ K

/-- **The projection map commutes with base change** (blueprint
`lemma-weil-pbc-projection-formula-base-change-naturality`, base change part): for a commutative
square `g' ≫ f = f' ≫ g`, `K` in `D(X_proét)` and `L` in `D(Y_proét)`, the square
```
Lg^*(Rf_*K ⊗ᴸ L) ──Lg^* π──▶ Lg^*Rf_*(K ⊗ᴸ Lf^*L) ──Ex_*──▶ Rf'_*Lg'^*(K ⊗ᴸ Lf^*L)
       │                                                          │
       ▼                                                          ▼
Lg^*Rf_*K ⊗ᴸ Lg^*L ──Ex_* ⊗ 1──▶ Rf'_*Lg'^*K ⊗ᴸ Lg^*L ──π──▶ Rf'_*(Lg'^*K ⊗ᴸ Lg'^*Lf^*L)
```
commutes, where the vertical arrows are the tensor comparisons of the derived pullbacks and the
bottom row ends with the square isomorphism `Lf'^*Lg^* ≅ Lg'^*Lf^*`. -/
lemma rightDerivedLowerStarProjectionMap_derivedBaseChangeMap (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app K).app L) ≫
        (derivedBaseChangeMap A sq).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        R((f')_*[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) =
      ((leftDerivedUpperStarTensorComparison A g).app (R((f)_*[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A sq).app K)).app (L((g)^*[A]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap A f').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) ≫
        R((f')_*[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          ((leftDerivedUpperStarSquareIso A sq).hom.app L)) :=
  Adjunction.rightAdjointProjectionMap_mate (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f') (leftDerivedUpperStarTensorComparison A f)
    (leftDerivedUpperStarTensorComparison A f') (leftDerivedUpperStarTensorComparison A g)
    (leftDerivedUpperStarTensorComparison A g') (leftDerivedUpperStarSquareIso A sq).hom
    (derivedBaseChangeMap A sq)
    (fun a b ↦ by
      have := leftDerivedUpperStarSquareIso_hom_tensor A sq a b
      rw [tensorHom_def] at this
      exact this)
    (derivedUpperStar_map_derivedBaseChangeMap_app_counit A sq) K L

end ProEtale

end AlgebraicGeometry
