/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Derived

/-!
# The tensor comparison of the derived pullback

- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.

See `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal` for an overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

section

open DerivedCategory Functor.OplaxMonoidal

variable [(g)^*[A].PreservesFlat]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, obtained by deriving the oplax monoidal structure `δ`
of `g^*`. It is the unique natural transformation such that, for `K, M` in `K(Y_ét)`, the square
```
  Lg^*(Qh K ⊗ᴸ Qh M) ──comparison──▶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)
          │                                    │
          │ Lg^*(μ Qh) ≫ counit                │ derivedTensorLeftDerivedUpperStarCounit
          ▼                                    ▼
   Qh(g^*(K ⊗ M)) ─────────Qh(δ g^*)──────▶ Qh(g^*K ⊗ g^*M)
```
commutes, the left vertical arrow being `leftDerivedUpperStarDerivedTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorComparison :
    leftDerivedUpperStarDerivedTensor A g ⟶ derivedTensorLeftDerivedUpperStar A g :=
  Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)

/-- The natural isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, whose underlying morphism is
`leftDerivedUpperStarTensorComparison`. -/
noncomputable def leftDerivedUpperStarTensorNatIso :
    leftDerivedUpperStarDerivedTensor A g ≅ derivedTensorLeftDerivedUpperStar A g :=
  -- `δ` is an isomorphism since `g^*` is strong monoidal.
  Functor.leftDerived₂NatIso _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (asIso (Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh))

@[simp]
lemma leftDerivedUpperStarTensorNatIso_hom :
    (leftDerivedUpperStarTensorNatIso A g).hom = leftDerivedUpperStarTensorComparison A g :=
  rfl

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is an isomorphism. -/
instance isIso_leftDerivedUpperStarTensorComparison :
    IsIso (leftDerivedUpperStarTensorComparison A g) :=
  (leftDerivedUpperStarTensorNatIso A g).isIso_hom

/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` in `D(Z_ét)`, for `K, M` in `D(Y_ét)`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj K).obj M) ≅
      ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).obj (L((g)^*[A]).obj M) :=
  ((leftDerivedUpperStarTensorNatIso A g).app K).app M

@[simp]
lemma leftDerivedUpperStarTensorIso_hom
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarTensorIso A g K M).hom =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

/-- For a fixed complex `M` on `Y`, the derived pullback commutes with tensoring by `M`:
`Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M`, naturally in `K`. That is, it compares the two functors
`K ↦ Lg^*(K ⊗ᴸ M)` and `K ↦ Lg^*K ⊗ᴸ Lg^*M` from `D(Y_ét)` to `D(Z_ét)`. This is
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso` with its second variable fixed. -/
noncomputable def derivedTensorRightCompLeftDerivedUpperStarIso
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    derivedTensorRight A Y M ⋙ L((g)^*[A]) ≅
      L((g)^*[A]) ⋙ derivedTensorRight A Z (L((g)^*[A]).obj M) :=
  NatIso.ofComponents (fun K ↦ leftDerivedUpperStarTensorIso A g K M) fun φ ↦
    NatTrans.congr_app ((leftDerivedUpperStarTensorNatIso A g).hom.naturality φ) M

end

/-- Tensoring with a complex pulled back along `g : Z ⟶ Y`, as a functor of the complex
downstairs: `N ↦ (K ↦ K ⊗ᴸ g^* N)`. -/
noncomputable def derivedTensorRightPullback :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  D((g)^*[A]) ⋙ derivedTensorRightFunctor A Z

/-- The canonical identification `Lg^* Λ_Y ≅ Λ_Z` of the units, the unit comparison asked for
in the TODO above.

The unit `Λ_Y` is the image in `D(Y_ét)` of the unit sheaf placed in degree `0`. Since `g^*` is
exact, `Lg^*` is computed by applying `g^*` degreewise, and `g^*` sends the unit sheaf of `Y`
to that of `Z` because it is strong monoidal. -/
noncomputable def leftDerivedUpperStarUnitIso : (L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
    ((g)^*[A].mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Functor.Monoidal.εIso (g)^*[A]).symm)

/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_unit :
    Nonempty ((L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :=
  ⟨leftDerivedUpperStarUnitIso A g⟩

/-- The derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)` is a monoidal functor for the derived tensor
products. This is the monoidality of derived pullback in blueprint
`def-weil-derived-pullback-tensor-hom` (within `sk-def-sf-operations`).

The structure isomorphisms are `leftDerivedUpperStarTensorIso` and the unit comparison of
`nonempty_iso_leftDerivedUpperStar_unit`; what is missing is their compatibility with the
associators and unitors of the derived tensor products, see the TODO in the module docstring. -/
theorem nonempty_monoidal_leftDerivedUpperStar [Etale.UpperStarPreservesFlat A] :
    Nonempty (L((g)^*[A])).Monoidal :=
  sorry

end Etale

end AlgebraicGeometry
